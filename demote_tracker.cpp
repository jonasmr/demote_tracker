#define INITGUID
#include <windows.h>
#include <evntrace.h>
#include <evntcons.h>
#include <tdh.h>
#include <tlhelp32.h>
#include <stdio.h>
#include <string>
#include <atomic>
#include <algorithm>
#include <unordered_map>
#include <vector>
#include <mutex>
#include <conio.h>

#include <io.h>
#include <shellapi.h>
#include <fcntl.h>
#include <dxgi1_4.h>

// Microsoft-Windows-DxgKrnl provider GUID
// {802ec45a-1e99-4b83-9920-87c98277ba9d}
DEFINE_GUID(DxgKrnlGuid, 0x802ec45a, 0x1e99, 0x4b83, 0x99, 0x20, 0x87, 0xc9, 0x82, 0x77, 0xba, 0x9d);

// Microsoft-Windows-Kernel-Process provider GUID
// {22FB2CD6-0E7B-422B-A0C7-2FAD1FD0E716}
DEFINE_GUID(KernelProcessGuid, 0x22FB2CD6, 0x0E7B, 0x422B, 0xA0, 0xC7, 0x2F, 0xAD, 0x1F, 0xD0, 0xE7, 0x16);
using std::wstring;

// Kernel Process event IDs
enum KernelProcessEventIds
{
	ProcessStart   = 1,
	ProcessStop	   = 2,
	ProcessRundown = 15, // DCStart - enumerates already-running processes
};

// Session name for our trace
static const wchar_t* SESSION_NAME = L"DemoteTrackerSession";

enum DxgKrnlEventIds
{
	// AdapterAllocation events (keyword: Resource 0x40)
	AdapterAllocation_Start	  = 33,
	AdapterAllocation_Stop	  = 34,
	AdapterAllocation_DCStart = 35,

	// DeviceAllocation events (keyword: Resource 0x40)
	DeviceAllocation_Start	 = 36,
	DeviceAllocation_Stop	 = 37,
	DeviceAllocation_DCStart = 38,

	// Other allocation events
	TerminateAllocation		   = 39,
	ProcessTerminateAllocation = 40,

	// ReferenceAllocations (keyword: References 0x4) - frequently seen
	ReferenceAllocations = 43,

	Adapter_Start	= 24,
	Adapter_Stop	= 25,
	Adapter_DCStart = 26,

	RenameAllocation_Start = 64,
	RenameAllocation_Stop  = 65,
	ReportSegment_Info	   = 78,

	DpiReportAdapter_Info = 110,

	// Memory events (keyword: Memory)
	ProcessAllocation_Start = 225,
	ProcessAllocation_Stop	= 226,

	// ProcessAllocationDetails (keyword: Resource 0x40)
	ProcessAllocationDetails_Start = 288,
	ProcessAllocationDetails_Stop  = 289,

	// RecycleRangeTracking (keyword: 0x80) - memory range management
	RecycleRangeTracking_Info1 = 301,
	RecycleRangeTracking_Info2 = 302,
	RecycleRangeTracking_Info3 = 303,

	PagingOpVirtualTransfer = 306,
	PagingOpNotifyResidency = 312,
	PagingOpSysmemCommit	= 313,
	PagingOpSysmemUncommit	= 314,

	// VidMm events (keyword: References 0x4)
	VidMmMakeResident = 320,
	VidMmEvict		  = 321,

	VidMmProcessBudgetChange			= 366,
	VidMmProcessUsageChange				= 367,
	VidMmProcessDemotedCommitmentChange = 370,
	VidMmProcessCommitmentChange		= 371,

	VidMmMakeResident_DCStart	= 374,
	TransferAllocationOwnership = 373,

};

enum ConsoleColor
{
	BLACK		 = 0,
	DARK_BLUE	 = 1,
	DARK_GREEN	 = 2,
	DARK_CYAN	 = 3,
	DARK_RED	 = 4,
	DARK_MAGENTA = 5,
	DARK_YELLOW	 = 6,
	GRAY		 = 7,
	DARK_GRAY	 = 8,
	BLUE		 = 9,
	GREEN		 = 10,
	CYAN		 = 11,
	RED			 = 12,
	MAGENTA		 = 13,
	YELLOW		 = 14,
	WHITE		 = 15
};
enum Prio
{
	PRIO_MIN,
	PRIO_LOW,
	PRIO_NORMAL,
	PRIO_HIGH,
	PRIO_MAX,
	PRIO_COUNT,
};

struct Process
{
	DWORD	pid;
	bool	isTracked = false;
	wstring imageFilename;
	wstring imagePath;
	int		nextFree = -1;
	void	Reset()
	{
		pid			  = (DWORD)-1;
		isTracked	  = false;
		imageFilename = L"";
		imagePath	  = L"";
	}
};

struct ProcessKey
{
	DWORD pid;
	PVOID pDxgAdapter;
	bool  operator==(const ProcessKey& other) const
	{
		return pid == other.pid && pDxgAdapter == other.pDxgAdapter;
	};
};

namespace std
{
template <>
struct hash<ProcessKey>
{
	std::size_t operator()(const ProcessKey& f) const noexcept
	{
		std::size_t h1 = std::hash<DWORD>{}(f.pid);
		std::size_t h2 = std::hash<PVOID>{}(f.pDxgAdapter);
		return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
	}
};
} // namespace std

struct ProcessMemory
{
	DWORD pid;
	PVOID pDxgAdapter;
	bool  isTracked;

	UINT64 CommitmentLocal;
	UINT64 CommitmentNonLocal;
	UINT64 UsageLocal;
	UINT64 UsageNonLocal;
	UINT64 CommitmentDemoted[PRIO_COUNT];

	void Reset()
	{
		CommitmentLocal	   = 0;
		CommitmentNonLocal = 0;
		UsageLocal		   = 0;
		UsageNonLocal	   = 0;
		memset(&CommitmentDemoted[0], 0, sizeof(CommitmentDemoted));
	}
};

#define MAX_SEGMENTS 32
struct Adapter
{
	std::wstring name;
	UINT64		 LocalMemory					  = 0;
	PVOID		 pDxgAdapter					  = 0;
	UINT64		 SegmentLocalMemory[MAX_SEGMENTS] = { 0 };
};

static TRACEHANDLE									 g_sessionHandle = 0;
static TRACEHANDLE									 g_traceHandle	 = INVALID_PROCESSTRACE_HANDLE;
static std::atomic<bool>							 g_traceStarted	 = false;
static CRITICAL_SECTION								 g_critSec;
static std::vector<Process>							 g_processes;
static int											 g_processFirstFree = -1;
static std::unordered_map<DWORD, int>				 g_pidToProcess;
static std::unordered_map<ProcessKey, ProcessMemory> g_processMemory;
static std::unordered_map<PVOID, Adapter>			 g_adapters;
static std::vector<wstring>							 g_trackedProcesses;
static bool											 g_verbose			 = false;
static bool											 g_detailedMode		 = false;
static int											 g_minSize			 = 0;
static bool											 g_detailedAvailable = false;
static HANDLE										 g_hRedrawEvent;

// Console Stuff
static HANDLE				  g_hConsoleOutput	   = NULL;
static HANDLE				  g_hConsoleInput	   = NULL;
static int					  g_consoleWidth	   = 80;
static int					  g_consoleHeight	   = 80;
static WORD					  g_originalAttributes = FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE;
static int					  g_lastWidth		   = 0;
static int					  g_lastHeight		   = 0;
static int					  g_currentX		   = 0;
static int					  g_currentY		   = 0;
static int					  g_currentColor	   = 0;
static std::vector<CHAR_INFO> g_chars;

// Colors
static int		   g_PrioTocolor[6]	  = { CYAN, YELLOW, DARK_YELLOW, RED, DARK_RED, MAGENTA };
static const char* g_prioNames[6]	  = { "?", "MIN", "LOW", "NORMAL", "HIGH", "MAX" };
static int		   g_adapterToColor[] = { YELLOW, WHITE, MAGENTA, RED, CYAN, WHITE, BLUE, GREEN };
static int		   g_numAdapterColors = sizeof(g_adapterToColor) / sizeof(g_adapterToColor[0]);

static FILE* g_LogFile = nullptr;

// #include <windows.h>
// #include <stdarg.h>
// #include <stdio.h>
static void dprintf(LPVOID pid, const char* fmt, ...);

Process* FindProcess(DWORD pid);

wstring FindProcName(DWORD pid)
{
	auto itr = g_pidToProcess.find(pid);
	if(itr != g_pidToProcess.end())
	{
		int index = (*itr).second;
		return g_processes[index].imageFilename;
	}
	return L"?";
}
ProcessMemory* FindProcessMemory(DWORD processId, PVOID pDxgAdapter)
{
	ProcessKey Key = { processId, pDxgAdapter };
	auto	   itr = g_processMemory.find(Key);
	if(itr != g_processMemory.end())
		return &(*itr).second;

	ProcessMemory* mem = &g_processMemory[Key];
	mem->isTracked	   = FindProcess(processId)->isTracked;
	return mem;
}

void FreeProcessMemory(DWORD pid)
{
	erase_if(g_processMemory, [pid](auto& itr) { return itr.first.pid == pid; });
}

Adapter* FindAdapter(PVOID pDxgAdapter)
{
	Adapter& a	  = g_adapters[pDxgAdapter];
	a.pDxgAdapter = pDxgAdapter;
	return &a;
}

Process* FindProcess(DWORD pid)
{
	auto	 itr = g_pidToProcess.find(pid);
	Process* res = nullptr;
	if(itr != g_pidToProcess.end())
	{
		int index = (*itr).second;
		res		  = &g_processes[index];
	}
	else
	{
		if(g_processFirstFree >= 0)
		{
			res				   = &g_processes[g_processFirstFree];
			g_processFirstFree = res->nextFree;
			res->nextFree	   = -1;
		}
		else
		{
			size_t s = g_processes.size();
			g_processes.push_back({});
			res = &g_processes[s];
		}
		res->Reset();
		res->pid			= pid;
		int index			= (int)(res - &g_processes[0]);
		g_pidToProcess[pid] = index;
	}
	if(res->nextFree >= 0)
		__debugbreak();
	if(res->pid != pid)
		__debugbreak();
	return res;
}
void FreeProcess(Process* process)
{
	int	 index = (int)(process - &g_processes[0]);
	auto itr   = g_pidToProcess.find(process->pid);
	if(itr != g_pidToProcess.end())
	{
		g_pidToProcess.erase(itr);
		process->pid = (DWORD)-1;
	}

	if(process->nextFree >= 0)
		__debugbreak();
	if(process->pid != (DWORD)-1)
		__debugbreak();
	process->nextFree  = g_processFirstFree;
	g_processFirstFree = index;
}

std::wstring ToLower(const std::wstring& str)
{
	std::wstring result = str;
	std::transform(result.begin(), result.end(), result.begin(), ::towlower);
	return result;
}

std::wstring GetFileName(const std::wstring& path)
{
	size_t pos = path.find_last_of(L"\\/");
	if(pos != std::wstring::npos)
	{
		return path.substr(pos + 1);
	}
	return path;
}

std::wstring GetProcessName(DWORD processId)
{
	std::wstring processName;
	HANDLE		 hProcess = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, processId);
	if(hProcess)
	{
		wchar_t path[MAX_PATH];
		DWORD	size = MAX_PATH;
		if(QueryFullProcessImageNameW(hProcess, 0, path, &size))
		{
			processName = GetFileName(path);
		}
		CloseHandle(hProcess);
	}
	return processName;
}

void FormatBytes(int64_t bytes, wchar_t* buffer, size_t bufferSize)
{
	const wchar_t* units[]	 = { L"B", L"KB", L"MB", L"GB", L"TB" };
	int			   unitIndex = 0;
	double		   value	 = (double)(bytes < 0 ? -bytes : bytes);

	while(value >= 1024.0 && unitIndex < 4)
	{
		value /= 1024.0;
		unitIndex++;
	}

	if(bytes < 0)
	{
		swprintf_s(buffer, bufferSize, L"-%.2f%s", value, units[unitIndex]);
	}
	else
	{
		swprintf_s(buffer, bufferSize, L"%.2f%s", value, units[unitIndex]);
	}
}

// Get property value from event by name
bool GetEventProperty(PEVENT_RECORD pEvent, PTRACE_EVENT_INFO pInfo, const wchar_t* propName, ULONGLONG* pValue)
{
	for(DWORD i = 0; i < pInfo->TopLevelPropertyCount; i++)
	{
		wchar_t* name = (wchar_t*)((PBYTE)pInfo + pInfo->EventPropertyInfoArray[i].NameOffset);
		if(_wcsicmp(name, propName) == 0)
		{
			PROPERTY_DATA_DESCRIPTOR dataDesc = {};
			dataDesc.PropertyName			  = (ULONGLONG)name;
			dataDesc.ArrayIndex				  = ULONG_MAX;

			DWORD propSize = 0;
			if(TdhGetPropertySize(pEvent, 0, nullptr, 1, &dataDesc, &propSize) == ERROR_SUCCESS)
			{
				if(propSize > 0 && propSize <= 8)
				{
					BYTE buffer[8] = { 0 };
					if(TdhGetProperty(pEvent, 0, nullptr, 1, &dataDesc, 8, buffer) == ERROR_SUCCESS)
					{
						if(propSize == 8)
							*pValue = *(ULONGLONG*)buffer;
						else if(propSize == 4)
							*pValue = *(ULONG*)buffer;
						else if(propSize == 2)
							*pValue = *(USHORT*)buffer;
						else if(propSize == 1)
							*pValue = *(UCHAR*)buffer;
						return true;
					}
				}
			}
			break;
		}
	}
	return false;
}

PTRACE_EVENT_INFO ExtractEventInformation(PEVENT_RECORD pEvent)
{
	DWORD bufferSize = 0;
	if(TdhGetEventInformation(pEvent, 0, nullptr, nullptr, &bufferSize) != ERROR_INSUFFICIENT_BUFFER)
	{
		return nullptr;
	}

	PTRACE_EVENT_INFO pInfo = (PTRACE_EVENT_INFO)malloc(bufferSize);
	if(!pInfo)
		return nullptr;

	if(TdhGetEventInformation(pEvent, 0, nullptr, pInfo, &bufferSize) != ERROR_SUCCESS)
	{
		free(pInfo);
		return nullptr;
	}
	return pInfo;
}

template <typename T>
T GetProperty(PEVENT_RECORD pEvent, const wchar_t* bleh)
{
	T						 r;
	PROPERTY_DATA_DESCRIPTOR dataDesc = {};
	dataDesc.PropertyName			  = (ULONGLONG)bleh;
	dataDesc.ArrayIndex				  = ULONG_MAX;

	DWORD propSize = 0;
	if(TdhGetPropertySize(pEvent, 0, nullptr, 1, &dataDesc, &propSize) == ERROR_SUCCESS)
	{
		if(propSize != sizeof(T))
			__debugbreak();
	}
	else
	{
		__debugbreak();
	}

	if(TdhGetProperty(pEvent, 0, nullptr, 1, &dataDesc, sizeof(T), (PBYTE)&r) != ERROR_SUCCESS)
		__debugbreak();
	return r;
}

wstring GetPropertyString(PEVENT_RECORD pEvent, const wchar_t* nameOffset)
{
	wstring					 r;
	PROPERTY_DATA_DESCRIPTOR dataDesc = {};
	dataDesc.PropertyName			  = (ULONGLONG)nameOffset;
	dataDesc.ArrayIndex				  = ULONG_MAX;
	DWORD propSize					  = 0;
	if(TdhGetPropertySize(pEvent, 0, nullptr, 1, &dataDesc, &propSize) == ERROR_SUCCESS && propSize > 0)
	{
		wchar_t* buffer = (wchar_t*)malloc(propSize);
		if(buffer && TdhGetProperty(pEvent, 0, nullptr, 1, &dataDesc, propSize, (PBYTE)buffer) == ERROR_SUCCESS)
		{
			wstring imageName = buffer;
			free(buffer);
			return imageName;
		}
		free(buffer);
		__debugbreak();
	}
	__debugbreak();
	return L"";
}

const wchar_t* GetPropertyOffset(PTRACE_EVENT_INFO pInfo, const wchar_t* searchPropName)
{
	for(DWORD i = 0; i < pInfo->TopLevelPropertyCount; i++)
	{
		wchar_t* propName = (wchar_t*)((PBYTE)pInfo + pInfo->EventPropertyInfoArray[i].NameOffset);
		if(_wcsicmp(propName, searchPropName) == 0)
		{
			return propName;
		}
	}
	return 0;
}

bool ProcessCheckTracked(const wstring& path)
{
	for(const wstring& tracked : g_trackedProcesses)
	{
		if(std::wcsstr(path.c_str(), tracked.c_str()))
			return true;
	}
	return false;
}

void OnProcessCreate(wstring imageName, DWORD processId, bool isRundown)
{
	(void)isRundown;
	std::wstring fileName  = GetFileName(imageName);
	Process*	 process   = FindProcess(processId);
	process->imageFilename = fileName;
	process->imagePath	   = imageName;
	process->isTracked	   = ProcessCheckTracked(imageName);
}
void OnProcessStop(DWORD pid)
{
	Process* process = FindProcess(pid);
	FreeProcess(process);
	FreeProcessMemory(pid);
}

void HandleProcessStart(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo		   = ExtractEventInformation(pEvent);
	static const wchar_t*	 propProcessId = GetPropertyOffset(pInfo, L"ProcessID");
	static const wchar_t*	 propImageName = GetPropertyOffset(pInfo, L"ImageName");
	DWORD					 pid		   = GetProperty<DWORD>(pEvent, propProcessId);
	wstring					 imageName	   = GetPropertyString(pEvent, propImageName);
	OnProcessCreate(imageName, pid, false);
}
void HandleProcessRundown(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo		   = ExtractEventInformation(pEvent);
	static const wchar_t*	 propProcessId = GetPropertyOffset(pInfo, L"ProcessID");
	static const wchar_t*	 propImageName = GetPropertyOffset(pInfo, L"ImageName");
	DWORD					 pid		   = GetProperty<DWORD>(pEvent, propProcessId);
	wstring					 imageName	   = GetPropertyString(pEvent, propImageName);
	OnProcessCreate(imageName, pid, true);
}
void HandleProcessStop(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo		   = ExtractEventInformation(pEvent);
	static const wchar_t*	 propProcessId = GetPropertyOffset(pInfo, L"ProcessID");
	DWORD					 pid		   = GetProperty<DWORD>(pEvent, propProcessId);
	OnProcessStop(pid);
}

void HandleProcessEvent(PEVENT_RECORD pEvent)
{
	USHORT eventId = pEvent->EventHeader.EventDescriptor.Id;

	switch(eventId)
	{
	case ProcessStart:
		HandleProcessStart(pEvent);
		break;
	case ProcessRundown:
		HandleProcessRundown(pEvent);
		break;
	case ProcessStop:
		HandleProcessStop(pEvent);
		break;
	}
}

struct GlobalAllocDescription
{
	PVOID			   VidMmGlobal;
	PVOID			   ProcessId;
	PVOID			   pDxgAdapter;
	UINT64			   Size;
	UINT32			   CommittedSegments;
	UINT32			   PreferredSegment;
	UINT32			   EvictedSegment;
	std::vector<PVOID> Allocs;
};

static std::unordered_map<PVOID, GlobalAllocDescription> g_GlobalAlloc;
static std::unordered_map<PVOID, PVOID>					 g_AllocToGlobal;

bool IsTracked(GlobalAllocDescription* al)
{
	PVOID	 pid  = al->ProcessId;
	Process* proc = FindProcess((DWORD)(INT64)pid);
	return proc->isTracked;
}

GlobalAllocDescription* FindOrAddGlobal(PVOID VidMmGlobal)
{
	auto itr = g_GlobalAlloc.find(VidMmGlobal);
	if(itr != g_GlobalAlloc.end())
	{
		return &(*itr).second;
	}
	return &g_GlobalAlloc[VidMmGlobal];
}
void RemoveGlobalAlloc(PVOID VidMmGlobal)
{
	auto itr = g_GlobalAlloc.find(VidMmGlobal);
	if(itr != g_GlobalAlloc.end())
	{
		g_GlobalAlloc.erase(itr);
	}
}
void HandleAdapterAllocationStart(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* prophProcessId			= GetPropertyOffset(pInfo, L"hProcessId");
	static const wchar_t* prophDevice				= GetPropertyOffset(pInfo, L"hDevice");
	static const wchar_t* proppDxgAdapter			= GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propFlags					= GetPropertyOffset(pInfo, L"Flags");
	static const wchar_t* propallocSize				= GetPropertyOffset(pInfo, L"allocSize");
	static const wchar_t* propulAlignment			= GetPropertyOffset(pInfo, L"ulAlignment");
	static const wchar_t* propdwReadSegment			= GetPropertyOffset(pInfo, L"dwReadSegment");
	static const wchar_t* propdwWriteSegment		= GetPropertyOffset(pInfo, L"dwWriteSegment");
	static const wchar_t* propPreferredSegment		= GetPropertyOffset(pInfo, L"PreferredSegment");
	static const wchar_t* propHintedBank			= GetPropertyOffset(pInfo, L"HintedBank");
	static const wchar_t* propdwEvictionSegment		= GetPropertyOffset(pInfo, L"dwEvictionSegment");
	static const wchar_t* propPriority				= GetPropertyOffset(pInfo, L"Priority");
	static const wchar_t* prophVidMmGlobalAlloc		= GetPropertyOffset(pInfo, L"hVidMmGlobalAlloc");
	static const wchar_t* prophDxgGlobalAlloc		= GetPropertyOffset(pInfo, L"hDxgGlobalAlloc");
	static const wchar_t* prophDxgSharedResource	= GetPropertyOffset(pInfo, L"hDxgSharedResource");
	static const wchar_t* propUsageVersion			= GetPropertyOffset(pInfo, L"UsageVersion");
	static const wchar_t* propUsageFlags			= GetPropertyOffset(pInfo, L"UsageFlags");
	static const wchar_t* propFormat				= GetPropertyOffset(pInfo, L"Format");
	static const wchar_t* propSwizzledFormat		= GetPropertyOffset(pInfo, L"SwizzledFormat");
	static const wchar_t* propByteOffset			= GetPropertyOffset(pInfo, L"ByteOffset");
	static const wchar_t* propWidth					= GetPropertyOffset(pInfo, L"Width");
	static const wchar_t* propHeight				= GetPropertyOffset(pInfo, L"Height");
	static const wchar_t* propPitch					= GetPropertyOffset(pInfo, L"Pitch");
	static const wchar_t* propDepth					= GetPropertyOffset(pInfo, L"Depth");
	static const wchar_t* propSlicePitch			= GetPropertyOffset(pInfo, L"SlicePitch");
	static const wchar_t* propBackingStoreWasPinned = GetPropertyOffset(pInfo, L"BackingStoreWasPinned");
	static const wchar_t* proppSectionObject		= GetPropertyOffset(pInfo, L"pSectionObject");
	static const wchar_t* propPhysicalAdapterIndex	= GetPropertyOffset(pInfo, L"PhysicalAdapterIndex");
	static const wchar_t* propPageTableOrDirectory	= GetPropertyOffset(pInfo, L"PageTableOrDirectory");

	PVOID  hProcessId		  = GetProperty<PVOID>(pEvent, prophProcessId);
	PVOID  hDevice			  = GetProperty<PVOID>(pEvent, prophDevice);
	PVOID  pDxgAdapter		  = GetProperty<PVOID>(pEvent, proppDxgAdapter);
	UINT32 Flags			  = GetProperty<UINT32>(pEvent, propFlags);
	UINT64 allocSize		  = GetProperty<UINT64>(pEvent, propallocSize);
	UINT32 ulAlignment		  = GetProperty<UINT32>(pEvent, propulAlignment);
	UINT32 dwReadSegment	  = GetProperty<UINT32>(pEvent, propdwReadSegment);
	UINT32 dwWriteSegment	  = GetProperty<UINT32>(pEvent, propdwWriteSegment);
	UINT32 PreferredSegment	  = GetProperty<UINT32>(pEvent, propPreferredSegment);
	UINT32 HintedBank		  = GetProperty<UINT32>(pEvent, propHintedBank);
	UINT32 dwEvictionSegment  = GetProperty<UINT32>(pEvent, propdwEvictionSegment);
	UINT32 Priority			  = GetProperty<UINT32>(pEvent, propPriority);
	PVOID  hVidMmGlobalAlloc  = GetProperty<PVOID>(pEvent, prophVidMmGlobalAlloc);
	PVOID  hDxgGlobalAlloc	  = GetProperty<PVOID>(pEvent, prophDxgGlobalAlloc);
	PVOID  hDxgSharedResource = GetProperty<PVOID>(pEvent, prophDxgSharedResource);
	UINT32 UsageVersion		  = GetProperty<UINT32>(pEvent, propUsageVersion);
	UINT32 UsageFlags		  = GetProperty<UINT32>(pEvent, propUsageFlags);
	UINT32 Format			  = GetProperty<UINT32>(pEvent, propFormat);
	UINT32 SwizzledFormat	  = GetProperty<UINT32>(pEvent, propSwizzledFormat);
	UINT32 ByteOffset		  = GetProperty<UINT32>(pEvent, propByteOffset);
	UINT32 Width			  = GetProperty<UINT32>(pEvent, propWidth);
	UINT32 Height			  = GetProperty<UINT32>(pEvent, propHeight);
	UINT32 Pitch			  = GetProperty<UINT32>(pEvent, propPitch);
	UINT32 Depth			  = GetProperty<UINT32>(pEvent, propDepth);
	UINT32 SlicePitch		  = GetProperty<UINT32>(pEvent, propSlicePitch);
	// BOOLEAN BackingStoreWasPinned = GetProperty<BOOLEAN>(pEvent, propBackingStoreWasPinned);
	// PVOID	pSectionObject		  = GetProperty<PVOID>(pEvent, proppSectionObject);
	// UINT16	PhysicalAdapterIndex  = GetProperty<UINT16>(pEvent, propPhysicalAdapterIndex);
	// BOOLEAN PageTableOrDirectory  = GetProperty<BOOLEAN>(pEvent, propPageTableOrDirectory);

	GlobalAllocDescription* pGlobal = FindOrAddGlobal(hVidMmGlobalAlloc);

	pGlobal->VidMmGlobal	   = hVidMmGlobalAlloc;
	pGlobal->ProcessId		   = hProcessId;
	pGlobal->pDxgAdapter	   = pDxgAdapter;
	pGlobal->Size			   = allocSize;
	pGlobal->CommittedSegments = 0;
	pGlobal->PreferredSegment  = PreferredSegment;
	pGlobal->EvictedSegment	   = dwEvictionSegment;
	dprintf(hProcessId, "ADAPTER_ALLOC %p / %8.5fKB\n", hVidMmGlobalAlloc, (float)allocSize / (1024.f));
}

void HandleAdapterAllocationStop(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* prophProcessId			= GetPropertyOffset(pInfo, L"hProcessId");
	static const wchar_t* prophDevice				= GetPropertyOffset(pInfo, L"hDevice");
	static const wchar_t* proppDxgAdapter			= GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propFlags					= GetPropertyOffset(pInfo, L"Flags");
	static const wchar_t* propallocSize				= GetPropertyOffset(pInfo, L"allocSize");
	static const wchar_t* propulAlignment			= GetPropertyOffset(pInfo, L"ulAlignment");
	static const wchar_t* propdwReadSegment			= GetPropertyOffset(pInfo, L"dwReadSegment");
	static const wchar_t* propdwWriteSegment		= GetPropertyOffset(pInfo, L"dwWriteSegment");
	static const wchar_t* propPreferredSegment		= GetPropertyOffset(pInfo, L"PreferredSegment");
	static const wchar_t* propHintedBank			= GetPropertyOffset(pInfo, L"HintedBank");
	static const wchar_t* propdwEvictionSegment		= GetPropertyOffset(pInfo, L"dwEvictionSegment");
	static const wchar_t* propPriority				= GetPropertyOffset(pInfo, L"Priority");
	static const wchar_t* prophVidMmGlobalAlloc		= GetPropertyOffset(pInfo, L"hVidMmGlobalAlloc");
	static const wchar_t* prophDxgGlobalAlloc		= GetPropertyOffset(pInfo, L"hDxgGlobalAlloc");
	static const wchar_t* prophDxgSharedResource	= GetPropertyOffset(pInfo, L"hDxgSharedResource");
	static const wchar_t* propUsageVersion			= GetPropertyOffset(pInfo, L"UsageVersion");
	static const wchar_t* propUsageFlags			= GetPropertyOffset(pInfo, L"UsageFlags");
	static const wchar_t* propFormat				= GetPropertyOffset(pInfo, L"Format");
	static const wchar_t* propSwizzledFormat		= GetPropertyOffset(pInfo, L"SwizzledFormat");
	static const wchar_t* propByteOffset			= GetPropertyOffset(pInfo, L"ByteOffset");
	static const wchar_t* propWidth					= GetPropertyOffset(pInfo, L"Width");
	static const wchar_t* propHeight				= GetPropertyOffset(pInfo, L"Height");
	static const wchar_t* propPitch					= GetPropertyOffset(pInfo, L"Pitch");
	static const wchar_t* propDepth					= GetPropertyOffset(pInfo, L"Depth");
	static const wchar_t* propSlicePitch			= GetPropertyOffset(pInfo, L"SlicePitch");
	static const wchar_t* propBackingStoreWasPinned = GetPropertyOffset(pInfo, L"BackingStoreWasPinned");
	static const wchar_t* proppSectionObject		= GetPropertyOffset(pInfo, L"pSectionObject");
	static const wchar_t* propPhysicalAdapterIndex	= GetPropertyOffset(pInfo, L"PhysicalAdapterIndex");
	static const wchar_t* propPageTableOrDirectory	= GetPropertyOffset(pInfo, L"PageTableOrDirectory");

	PVOID  hProcessId			 = GetProperty<PVOID>(pEvent, prophProcessId);
	PVOID  hDevice				 = GetProperty<PVOID>(pEvent, prophDevice);
	PVOID  pDxgAdapter			 = GetProperty<PVOID>(pEvent, proppDxgAdapter);
	UINT32 Flags				 = GetProperty<UINT32>(pEvent, propFlags);
	UINT64 allocSize			 = GetProperty<UINT64>(pEvent, propallocSize);
	UINT32 ulAlignment			 = GetProperty<UINT32>(pEvent, propulAlignment);
	UINT32 dwReadSegment		 = GetProperty<UINT32>(pEvent, propdwReadSegment);
	UINT32 dwWriteSegment		 = GetProperty<UINT32>(pEvent, propdwWriteSegment);
	UINT32 PreferredSegment		 = GetProperty<UINT32>(pEvent, propPreferredSegment);
	UINT32 HintedBank			 = GetProperty<UINT32>(pEvent, propHintedBank);
	UINT32 dwEvictionSegment	 = GetProperty<UINT32>(pEvent, propdwEvictionSegment);
	UINT32 Priority				 = GetProperty<UINT32>(pEvent, propPriority);
	PVOID  hVidMmGlobalAlloc	 = GetProperty<PVOID>(pEvent, prophVidMmGlobalAlloc);
	PVOID  hDxgGlobalAlloc		 = GetProperty<PVOID>(pEvent, prophDxgGlobalAlloc);
	PVOID  hDxgSharedResource	 = GetProperty<PVOID>(pEvent, prophDxgSharedResource);
	UINT32 UsageVersion			 = GetProperty<UINT32>(pEvent, propUsageVersion);
	UINT32 UsageFlags			 = GetProperty<UINT32>(pEvent, propUsageFlags);
	UINT32 Format				 = GetProperty<UINT32>(pEvent, propFormat);
	UINT32 SwizzledFormat		 = GetProperty<UINT32>(pEvent, propSwizzledFormat);
	UINT32 ByteOffset			 = GetProperty<UINT32>(pEvent, propByteOffset);
	UINT32 Width				 = GetProperty<UINT32>(pEvent, propWidth);
	UINT32 Height				 = GetProperty<UINT32>(pEvent, propHeight);
	UINT32 Pitch				 = GetProperty<UINT32>(pEvent, propPitch);
	UINT32 Depth				 = GetProperty<UINT32>(pEvent, propDepth);
	UINT32 SlicePitch			 = GetProperty<UINT32>(pEvent, propSlicePitch);
	DWORD  BackingStoreWasPinned = GetProperty<DWORD>(pEvent, propBackingStoreWasPinned);
	PVOID  pSectionObject		 = GetProperty<PVOID>(pEvent, proppSectionObject);
	UINT16 PhysicalAdapterIndex	 = GetProperty<UINT16>(pEvent, propPhysicalAdapterIndex);
	DWORD  PageTableOrDirectory	 = GetProperty<DWORD>(pEvent, propPageTableOrDirectory);
	RemoveGlobalAlloc(hVidMmGlobalAlloc);
}

void HandleDeviceAllocationStart(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* prophProcessId				   = GetPropertyOffset(pInfo, L"hProcessId");
	static const wchar_t* prophDevice					   = GetPropertyOffset(pInfo, L"hDevice");
	static const wchar_t* proppDxgAdapter				   = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* prophVidMmAlloc				   = GetPropertyOffset(pInfo, L"hVidMmAlloc");
	static const wchar_t* prophVidMmGlobalAlloc			   = GetPropertyOffset(pInfo, L"hVidMmGlobalAlloc");
	static const wchar_t* prophDxgResource				   = GetPropertyOffset(pInfo, L"hDxgResource");
	static const wchar_t* prophDxgSharedResource		   = GetPropertyOffset(pInfo, L"hDxgSharedResource");
	static const wchar_t* prophThunkAllocation			   = GetPropertyOffset(pInfo, L"hThunkAllocation");
	static const wchar_t* prophThunkResource			   = GetPropertyOffset(pInfo, L"hThunkResource");
	static const wchar_t* propPrivateRuntimeResourceHandle = GetPropertyOffset(pInfo, L"PrivateRuntimeResourceHandle");
	static const wchar_t* proppVirtualAddress			   = GetPropertyOffset(pInfo, L"pVirtualAddress");
	static const wchar_t* prophProcessAllocDetails		   = GetPropertyOffset(pInfo, L"hProcessAllocDetails");
	static const wchar_t* prophOtherPartitionHandle		   = GetPropertyOffset(pInfo, L"hOtherPartitionHandle");

	PVOID  hProcessId					= GetProperty<PVOID>(pEvent, prophProcessId);
	PVOID  hDevice						= GetProperty<PVOID>(pEvent, prophDevice);
	PVOID  pDxgAdapter					= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	PVOID  hVidMmAlloc					= GetProperty<PVOID>(pEvent, prophVidMmAlloc);
	PVOID  hVidMmGlobalAlloc			= GetProperty<PVOID>(pEvent, prophVidMmGlobalAlloc);
	PVOID  hDxgResource					= GetProperty<PVOID>(pEvent, prophDxgResource);
	PVOID  hDxgSharedResource			= GetProperty<PVOID>(pEvent, prophDxgSharedResource);
	PVOID  hThunkAllocation				= GetProperty<PVOID>(pEvent, prophThunkAllocation);
	PVOID  hThunkResource				= GetProperty<PVOID>(pEvent, prophThunkResource);
	PVOID  PrivateRuntimeResourceHandle = GetProperty<PVOID>(pEvent, propPrivateRuntimeResourceHandle);
	PVOID  pVirtualAddress				= GetProperty<PVOID>(pEvent, proppVirtualAddress);
	PVOID  hProcessAllocDetails			= GetProperty<PVOID>(pEvent, prophProcessAllocDetails);
	UINT32 hOtherPartitionHandle		= GetProperty<UINT32>(pEvent, prophOtherPartitionHandle);

	GlobalAllocDescription* pGlobal = FindOrAddGlobal(hVidMmGlobalAlloc);
	pGlobal->Allocs.push_back(hVidMmAlloc);
	g_AllocToGlobal[hVidMmAlloc] = hVidMmGlobalAlloc;

	dprintf(hProcessId, "DEVICE_ALLOC %p / %p\n", hVidMmGlobalAlloc, hVidMmAlloc);
}

void HandleDeviceAllocationStop(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* prophProcessId				   = GetPropertyOffset(pInfo, L"hProcessId");
	static const wchar_t* prophDevice					   = GetPropertyOffset(pInfo, L"hDevice");
	static const wchar_t* proppDxgAdapter				   = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* prophVidMmAlloc				   = GetPropertyOffset(pInfo, L"hVidMmAlloc");
	static const wchar_t* prophVidMmGlobalAlloc			   = GetPropertyOffset(pInfo, L"hVidMmGlobalAlloc");
	static const wchar_t* prophDxgResource				   = GetPropertyOffset(pInfo, L"hDxgResource");
	static const wchar_t* prophDxgSharedResource		   = GetPropertyOffset(pInfo, L"hDxgSharedResource");
	static const wchar_t* prophThunkAllocation			   = GetPropertyOffset(pInfo, L"hThunkAllocation");
	static const wchar_t* prophThunkResource			   = GetPropertyOffset(pInfo, L"hThunkResource");
	static const wchar_t* propPrivateRuntimeResourceHandle = GetPropertyOffset(pInfo, L"PrivateRuntimeResourceHandle");
	static const wchar_t* proppVirtualAddress			   = GetPropertyOffset(pInfo, L"pVirtualAddress");
	static const wchar_t* prophProcessAllocDetails		   = GetPropertyOffset(pInfo, L"hProcessAllocDetails");
	static const wchar_t* prophOtherPartitionHandle		   = GetPropertyOffset(pInfo, L"hOtherPartitionHandle");

	PVOID  hProcessId					= GetProperty<PVOID>(pEvent, prophProcessId);
	PVOID  hDevice						= GetProperty<PVOID>(pEvent, prophDevice);
	PVOID  pDxgAdapter					= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	PVOID  hVidMmAlloc					= GetProperty<PVOID>(pEvent, prophVidMmAlloc);
	PVOID  hVidMmGlobalAlloc			= GetProperty<PVOID>(pEvent, prophVidMmGlobalAlloc);
	PVOID  hDxgResource					= GetProperty<PVOID>(pEvent, prophDxgResource);
	PVOID  hDxgSharedResource			= GetProperty<PVOID>(pEvent, prophDxgSharedResource);
	PVOID  hThunkAllocation				= GetProperty<PVOID>(pEvent, prophThunkAllocation);
	PVOID  hThunkResource				= GetProperty<PVOID>(pEvent, prophThunkResource);
	PVOID  PrivateRuntimeResourceHandle = GetProperty<PVOID>(pEvent, propPrivateRuntimeResourceHandle);
	PVOID  pVirtualAddress				= GetProperty<PVOID>(pEvent, proppVirtualAddress);
	PVOID  hProcessAllocDetails			= GetProperty<PVOID>(pEvent, prophProcessAllocDetails);
	UINT32 hOtherPartitionHandle		= GetProperty<UINT32>(pEvent, prophOtherPartitionHandle);

	GlobalAllocDescription* pGlobal = FindOrAddGlobal(hVidMmGlobalAlloc);
	{
		auto itr = std::find(pGlobal->Allocs.begin(), pGlobal->Allocs.end(), hVidMmAlloc);
		if(itr != pGlobal->Allocs.end())
		{
			pGlobal->Allocs.erase(itr);
		}
	}
	{
		auto itr = g_AllocToGlobal.find(hVidMmAlloc);
		if(itr != g_AllocToGlobal.end())
			g_AllocToGlobal.erase(itr);
	}
}

void HandlePagingOpVirtualTransfer(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* proppDxgAdapter				= GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* prophDmaBuffer				= GetPropertyOffset(pInfo, L"hDmaBuffer");
	static const wchar_t* propContinueNextBuffer		= GetPropertyOffset(pInfo, L"ContinueNextBuffer");
	static const wchar_t* prophAllocationGlobalHandle	= GetPropertyOffset(pInfo, L"hAllocationGlobalHandle");
	static const wchar_t* propAllocationOffset			= GetPropertyOffset(pInfo, L"AllocationOffset");
	static const wchar_t* propTransferSize				= GetPropertyOffset(pInfo, L"TransferSize");
	static const wchar_t* propSourceSegmentId			= GetPropertyOffset(pInfo, L"SourceSegmentId");
	static const wchar_t* propDestinationSegmentId		= GetPropertyOffset(pInfo, L"DestinationSegmentId");
	static const wchar_t* propSourceVirtualAddress		= GetPropertyOffset(pInfo, L"SourceVirtualAddress");
	static const wchar_t* propDestinationVirtualAddress = GetPropertyOffset(pInfo, L"DestinationVirtualAddress");
	static const wchar_t* propSourcePageTable			= GetPropertyOffset(pInfo, L"SourcePageTable");
	static const wchar_t* propTransferDirection			= GetPropertyOffset(pInfo, L"TransferDirection");
	static const wchar_t* propTransferFlags				= GetPropertyOffset(pInfo, L"TransferFlags");
	static const wchar_t* propDestinationPageTable		= GetPropertyOffset(pInfo, L"DestinationPageTable");
	static const wchar_t* propSourceSegmentOffset		= GetPropertyOffset(pInfo, L"SourceSegmentOffset");
	static const wchar_t* propDestinationSegmentOffset	= GetPropertyOffset(pInfo, L"DestinationSegmentOffset");

	PVOID  pDxgAdapter				 = GetProperty<PVOID>(pEvent, proppDxgAdapter);
	PVOID  hDmaBuffer				 = GetProperty<PVOID>(pEvent, prophDmaBuffer);
	DWORD  ContinueNextBuffer		 = GetProperty<DWORD>(pEvent, propContinueNextBuffer);
	PVOID  hAllocationGlobalHandle	 = GetProperty<PVOID>(pEvent, prophAllocationGlobalHandle);
	UINT64 AllocationOffset			 = GetProperty<UINT64>(pEvent, propAllocationOffset);
	UINT64 TransferSize				 = GetProperty<UINT64>(pEvent, propTransferSize);
	UINT32 SourceSegmentId			 = GetProperty<UINT32>(pEvent, propSourceSegmentId);
	UINT32 DestinationSegmentId		 = GetProperty<UINT32>(pEvent, propDestinationSegmentId);
	UINT64 SourceVirtualAddress		 = GetProperty<UINT64>(pEvent, propSourceVirtualAddress);
	UINT64 DestinationVirtualAddress = GetProperty<UINT64>(pEvent, propDestinationVirtualAddress);
	UINT64 SourcePageTable			 = GetProperty<UINT64>(pEvent, propSourcePageTable);
	UINT32 TransferDirection		 = GetProperty<UINT32>(pEvent, propTransferDirection);
	UINT32 TransferFlags			 = GetProperty<UINT32>(pEvent, propTransferFlags);
	UINT64 DestinationPageTable		 = GetProperty<UINT64>(pEvent, propDestinationPageTable);
	UINT64 SourceSegmentOffset		 = GetProperty<UINT64>(pEvent, propSourceSegmentOffset);
	UINT64 DestinationSegmentOffset	 = GetProperty<UINT64>(pEvent, propDestinationSegmentOffset);


	GlobalAllocDescription* pGlobal					= FindOrAddGlobal(hAllocationGlobalHandle);
	dprintf(pGlobal->ProcessId, "OpVirtualTransfer %p :: %04x segment %d -> %d .. %8.3fKB\n", hAllocationGlobalHandle, pGlobal-> CommittedSegments, SourceSegmentId, DestinationSegmentId, pGlobal->Size / (1024.f));

}

void HandlePagingOpNotifyResidency(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* proppDxgAdapter			  = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* prophDmaBuffer			  = GetPropertyOffset(pInfo, L"hDmaBuffer");
	static const wchar_t* propContinueNextBuffer	  = GetPropertyOffset(pInfo, L"ContinueNextBuffer");
	static const wchar_t* prophAllocationGlobalHandle = GetPropertyOffset(pInfo, L"hAllocationGlobalHandle");
	static const wchar_t* propSegmentId				  = GetPropertyOffset(pInfo, L"SegmentId");
	static const wchar_t* propSegmentOffset			  = GetPropertyOffset(pInfo, L"SegmentOffset");
	static const wchar_t* propFlags					  = GetPropertyOffset(pInfo, L"Flags");

	PVOID					pDxgAdapter				= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	PVOID					hDmaBuffer				= GetProperty<PVOID>(pEvent, prophDmaBuffer);
	DWORD					ContinueNextBuffer		= GetProperty<DWORD>(pEvent, propContinueNextBuffer);
	PVOID					hAllocationGlobalHandle = GetProperty<PVOID>(pEvent, prophAllocationGlobalHandle);
	UINT32					SegmentId				= GetProperty<UINT32>(pEvent, propSegmentId);
	UINT64					SegmentOffset			= GetProperty<UINT64>(pEvent, propSegmentOffset);
	UINT32					Flags					= GetProperty<UINT32>(pEvent, propFlags);
	GlobalAllocDescription* pGlobal					= FindOrAddGlobal(hAllocationGlobalHandle);

	dprintf(pGlobal->ProcessId, "NotifyResidency %p :: segment %d\n", hAllocationGlobalHandle, SegmentId);
}

void HandlePagingOpSysmemCommit(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* proppDxgAdapter			  = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* prophAllocationGlobalHandle = GetPropertyOffset(pInfo, L"hAllocationGlobalHandle");
	static const wchar_t* propSegmentId				  = GetPropertyOffset(pInfo, L"SegmentId");

	PVOID					pDxgAdapter				= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	PVOID					hAllocationGlobalHandle = GetProperty<PVOID>(pEvent, prophAllocationGlobalHandle);
	UINT32					SegmentId				= GetProperty<UINT32>(pEvent, propSegmentId);
	GlobalAllocDescription* pGlobal					= FindOrAddGlobal(hAllocationGlobalHandle);
	if(IsTracked(pGlobal))
	{
		OutputDebugStringA("LAL");
	}
	pGlobal->CommittedSegments |= (1 << SegmentId);
	dprintf(pGlobal->ProcessId, "SysmemCommitSegment %p [%x] / %8.5fKB\n", hAllocationGlobalHandle, pGlobal->CommittedSegments, pGlobal->Size / (1024.f));
}

void HandlePagingOpSysmemUncommit(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* proppDxgAdapter			  = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* prophAllocationGlobalHandle = GetPropertyOffset(pInfo, L"hAllocationGlobalHandle");
	static const wchar_t* propSegmentId				  = GetPropertyOffset(pInfo, L"SegmentId");

	PVOID					pDxgAdapter				= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	PVOID					hAllocationGlobalHandle = GetProperty<PVOID>(pEvent, prophAllocationGlobalHandle);
	UINT32					SegmentId				= GetProperty<UINT32>(pEvent, propSegmentId);
	GlobalAllocDescription* pGlobal					= FindOrAddGlobal(hAllocationGlobalHandle);
	if(IsTracked(pGlobal))
	{
		OutputDebugStringA("LAL");
	}
	pGlobal->CommittedSegments &= ~(1 << SegmentId);
	dprintf(pGlobal->ProcessId, "SysmemUncommitSegment %p [%x] %d / %8.5fMB\n", hAllocationGlobalHandle, pGlobal->CommittedSegments, SegmentId, pGlobal->Size / (1024.f));
}

void HandleVidMmProcessBudgetChange(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo					  = ExtractEventInformation(pEvent);
	static const wchar_t*	 propNewBudget			  = GetPropertyOffset(pInfo, L"NewBudget");
	static const wchar_t*	 propOldBudget			  = GetPropertyOffset(pInfo, L"OldBudget");
	static const wchar_t*	 proppDxgAdapter		  = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t*	 propProcessId			  = GetPropertyOffset(pInfo, L"ProcessId");
	static const wchar_t*	 propPhysicalAdapterIndex = GetPropertyOffset(pInfo, L"PhysicalAdapterIndex");
	static const wchar_t*	 propNewPriorityBand	  = GetPropertyOffset(pInfo, L"NewPriorityBand");
	static const wchar_t*	 propOldPriorityBand	  = GetPropertyOffset(pInfo, L"OldPriorityBand");
	static const wchar_t*	 propNewVisibilityState	  = GetPropertyOffset(pInfo, L"NewVisibilityState");
	static const wchar_t*	 propOldVisibilityState	  = GetPropertyOffset(pInfo, L"OldVisibilityState");
	static const wchar_t*	 propMemorySegmentGroup	  = GetPropertyOffset(pInfo, L"MemorySegmentGroup");

	UINT64 NewBudget			= GetProperty<UINT64>(pEvent, propNewBudget);
	UINT64 OldBudget			= GetProperty<UINT64>(pEvent, propOldBudget);
	PVOID  pDxgAdapter			= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	UINT32 ProcessId			= GetProperty<UINT32>(pEvent, propProcessId);
	UINT16 PhysicalAdapterIndex = GetProperty<UINT16>(pEvent, propPhysicalAdapterIndex);
	UINT8  NewPriorityBand		= GetProperty<UINT8>(pEvent, propNewPriorityBand);
	UINT8  OldPriorityBand		= GetProperty<UINT8>(pEvent, propOldPriorityBand);
	UINT8  NewVisibilityState	= GetProperty<UINT8>(pEvent, propNewVisibilityState);
	UINT8  OldVisibilityState	= GetProperty<UINT8>(pEvent, propOldVisibilityState);
	UINT8  MemorySegmentGroup	= GetProperty<UINT8>(pEvent, propMemorySegmentGroup);
}

void HandleVidMmProcessUsageChange(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* propNewUsage			   = GetPropertyOffset(pInfo, L"NewUsage");
	static const wchar_t* propOldUsage			   = GetPropertyOffset(pInfo, L"OldUsage");
	static const wchar_t* proppDxgAdapter		   = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propProcessId			   = GetPropertyOffset(pInfo, L"ProcessId");
	static const wchar_t* propPhysicalAdapterIndex = GetPropertyOffset(pInfo, L"PhysicalAdapterIndex");
	static const wchar_t* propMemorySegmentGroup   = GetPropertyOffset(pInfo, L"MemorySegmentGroup");

	UINT64 NewUsage				= GetProperty<UINT64>(pEvent, propNewUsage);
	UINT64 OldUsage				= GetProperty<UINT64>(pEvent, propOldUsage);
	PVOID  pDxgAdapter			= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	UINT32 ProcessId			= GetProperty<UINT32>(pEvent, propProcessId);
	UINT16 PhysicalAdapterIndex = GetProperty<UINT16>(pEvent, propPhysicalAdapterIndex);
	UINT8  MemorySegmentGroup	= GetProperty<UINT8>(pEvent, propMemorySegmentGroup);

	ProcessMemory* memory = FindProcessMemory(ProcessId, pDxgAdapter);
	if(MemorySegmentGroup)
		memory->UsageNonLocal = NewUsage;
	else
		memory->UsageLocal = NewUsage;
}

void HandleVidMmProcessDemotedCommitmentChange(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* propCommitment		   = GetPropertyOffset(pInfo, L"Commitment");
	static const wchar_t* propOldCommitment		   = GetPropertyOffset(pInfo, L"OldCommitment");
	static const wchar_t* proppDxgAdapter		   = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propProcessId			   = GetPropertyOffset(pInfo, L"ProcessId");
	static const wchar_t* propPhysicalAdapterIndex = GetPropertyOffset(pInfo, L"PhysicalAdapterIndex");
	static const wchar_t* propPriorityClass		   = GetPropertyOffset(pInfo, L"PriorityClass");

	UINT64 Commitment			= GetProperty<UINT64>(pEvent, propCommitment);
	UINT64 OldCommitment		= GetProperty<UINT64>(pEvent, propOldCommitment);
	PVOID  pDxgAdapter			= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	UINT32 ProcessId			= GetProperty<UINT32>(pEvent, propProcessId);
	UINT16 PhysicalAdapterIndex = GetProperty<UINT16>(pEvent, propPhysicalAdapterIndex);
	UINT8  PriorityClass		= GetProperty<UINT8>(pEvent, propPriorityClass);

	int			   prio				= PRIO_MAX < PriorityClass ? PRIO_MAX : PriorityClass;
	ProcessMemory* memory			= FindProcessMemory(ProcessId, pDxgAdapter);
	memory->CommitmentDemoted[prio] = Commitment;

	if(g_verbose)
	{
		fprintf(g_LogFile, "DEM %lld <- %lld %p, %d. %d %d\n", Commitment, OldCommitment, pDxgAdapter, ProcessId, PhysicalAdapterIndex, PriorityClass);
		fflush(g_LogFile);
	}
}

void HandleVidMmProcessCommitmentChange(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* propCommitment		   = GetPropertyOffset(pInfo, L"Commitment");
	static const wchar_t* propOldCommitment		   = GetPropertyOffset(pInfo, L"OldCommitment");
	static const wchar_t* proppDxgAdapter		   = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propProcessId			   = GetPropertyOffset(pInfo, L"ProcessId");
	static const wchar_t* propPhysicalAdapterIndex = GetPropertyOffset(pInfo, L"PhysicalAdapterIndex");
	static const wchar_t* propMemorySegmentGroup   = GetPropertyOffset(pInfo, L"MemorySegmentGroup");

	UINT64 Commitment			= GetProperty<UINT64>(pEvent, propCommitment);
	UINT64 OldCommitment		= GetProperty<UINT64>(pEvent, propOldCommitment);
	PVOID  pDxgAdapter			= GetProperty<PVOID>(pEvent, proppDxgAdapter);
	UINT32 ProcessId			= GetProperty<UINT32>(pEvent, propProcessId);
	UINT16 PhysicalAdapterIndex = GetProperty<UINT16>(pEvent, propPhysicalAdapterIndex);
	UINT8  MemorySegmentGroup	= GetProperty<UINT8>(pEvent, propMemorySegmentGroup);
}

void HandleReportSegment(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* propulSegmentId			 = GetPropertyOffset(pInfo, L"ulSegmentId");
	static const wchar_t* proppDxgAdapter			 = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propBaseAddress			 = GetPropertyOffset(pInfo, L"BaseAddress");
	static const wchar_t* propCpuTranslatedAddress	 = GetPropertyOffset(pInfo, L"CpuTranslatedAddress");
	static const wchar_t* propSize					 = GetPropertyOffset(pInfo, L"Size");
	static const wchar_t* propNbOfBanks				 = GetPropertyOffset(pInfo, L"NbOfBanks");
	static const wchar_t* propFlags					 = GetPropertyOffset(pInfo, L"Flags");
	static const wchar_t* propCommitLimit			 = GetPropertyOffset(pInfo, L"CommitLimit");
	static const wchar_t* propSystemMemoryEndAddress = GetPropertyOffset(pInfo, L"SystemMemoryEndAddress");
	static const wchar_t* propMemorySegmentGroup	 = GetPropertyOffset(pInfo, L"MemorySegmentGroup");

	UINT32 ulSegmentId			  = GetProperty<UINT32>(pEvent, propulSegmentId);
	LPVOID pDxgAdapter			  = GetProperty<LPVOID>(pEvent, proppDxgAdapter);
	UINT64 BaseAddress			  = GetProperty<UINT64>(pEvent, propBaseAddress);
	UINT64 CpuTranslatedAddress	  = GetProperty<UINT64>(pEvent, propCpuTranslatedAddress);
	UINT64 Size					  = GetProperty<UINT64>(pEvent, propSize);
	UINT32 NbOfBanks			  = GetProperty<UINT32>(pEvent, propNbOfBanks);
	UINT32 Flags				  = GetProperty<UINT32>(pEvent, propFlags);
	UINT64 CommitLimit			  = GetProperty<UINT64>(pEvent, propCommitLimit);
	LPVOID SystemMemoryEndAddress = GetProperty<LPVOID>(pEvent, propSystemMemoryEndAddress);
	UINT8  MemorySegmentGroup	  = GetProperty<UINT8>(pEvent, propMemorySegmentGroup);

	typedef enum _D3DKMT_MEMORY_SEGMENT_GROUP
	{
		D3DKMT_MEMORY_SEGMENT_GROUP_LOCAL,
		D3DKMT_MEMORY_SEGMENT_GROUP_NON_LOCAL
	} D3DKMT_MEMORY_SEGMENT_GROUP;

	Adapter* adapter = FindAdapter(pDxgAdapter);

	dprintf(0, "Report Segment %p/%ls // %d grp %d :: %8.5fMB\n", pDxgAdapter, adapter->name.c_str(), ulSegmentId, MemorySegmentGroup, Size / (1024.f * 1024.f));

	if(MemorySegmentGroup == D3DKMT_MEMORY_SEGMENT_GROUP_LOCAL)
		adapter->SegmentLocalMemory[ulSegmentId % MAX_SEGMENTS] = Size;
	else
		adapter->SegmentLocalMemory[ulSegmentId % MAX_SEGMENTS] = 0;
	UINT64 Local = 0;
	for(UINT64 Memory : adapter->SegmentLocalMemory)
	{
		Local += Memory;
	}
	adapter->LocalMemory = Local;

	fprintf(g_LogFile,
			"Adapter Segment %ls/%d: %6.fMB / %s\n",
			adapter->name.c_str(),
			ulSegmentId,
			Size / (1024.f * 1024.f),
			MemorySegmentGroup == D3DKMT_MEMORY_SEGMENT_GROUP_LOCAL ? "Local" : "NonLocal");
	fflush(g_LogFile);
}

void HandleAdapterStart(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* propulSegmentId				 = GetPropertyOffset(pInfo, L"ulSegmentId");
	static const wchar_t* proppDxgAdapter				 = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propApertureSegmentCommitLimit = GetPropertyOffset(pInfo, L"ApertureSegmentCommitLimit");

	LPVOID pDxgAdapter				  = GetProperty<LPVOID>(pEvent, proppDxgAdapter);
	UINT64 ApertureSegmentCommitLimit = GetProperty<UINT64>(pEvent, propApertureSegmentCommitLimit);
}
void HandleDpiReportAdapter(PEVENT_RECORD pEvent)
{
	static PTRACE_EVENT_INFO pInfo = ExtractEventInformation(pEvent);

	static const wchar_t* proppDxgAdapter = GetPropertyOffset(pInfo, L"pDxgAdapter");
	static const wchar_t* propAdapterLuid = GetPropertyOffset(pInfo, L"AdapterLuid");

	LPVOID		   pDxgAdapter = GetProperty<LPVOID>(pEvent, proppDxgAdapter);
	UINT64		   Luid		   = GetProperty<UINT64>(pEvent, propAdapterLuid);
	IDXGIFactory4* pFactory;
	CreateDXGIFactory2(0, __uuidof(IDXGIFactory4), (void**)&pFactory);
	LUID luid;
	memcpy(&luid, &Luid, sizeof(luid));
	IDXGIAdapter1* pAdapter;

	pFactory->EnumAdapterByLuid(luid, __uuidof(IDXGIAdapter1), (void**)&pAdapter);

	DXGI_ADAPTER_DESC1 desc;
	pAdapter->GetDesc1(&desc);

	Adapter* adapter = FindAdapter(pDxgAdapter);
	adapter->name	 = desc.Description;

	pFactory->Release();
	pAdapter->Release();
}

void HandleDxgKrnlEvent(PEVENT_RECORD pEvent)
{
	USHORT eventId = pEvent->EventHeader.EventDescriptor.Id;

	switch(eventId)
	{
	case VidMmProcessBudgetChange:
		HandleVidMmProcessBudgetChange(pEvent);
		break;
	case VidMmProcessUsageChange:
		HandleVidMmProcessUsageChange(pEvent);
		break;
	case VidMmProcessDemotedCommitmentChange:
		HandleVidMmProcessDemotedCommitmentChange(pEvent);
		break;
	case VidMmProcessCommitmentChange:
		HandleVidMmProcessCommitmentChange(pEvent);
		break;
	case ReportSegment_Info:
		HandleReportSegment(pEvent);
		break;
	case Adapter_Start:
	case Adapter_DCStart:
		HandleAdapterStart(pEvent);
		break;
	case DpiReportAdapter_Info:
		HandleDpiReportAdapter(pEvent);
		break;
	case AdapterAllocation_Start:
	case AdapterAllocation_DCStart:
		HandleAdapterAllocationStart(pEvent);
		break;
	case AdapterAllocation_Stop:
		HandleAdapterAllocationStop(pEvent);
		break;

	case DeviceAllocation_Start:
	case DeviceAllocation_DCStart:
		HandleDeviceAllocationStart(pEvent);
		break;
	case DeviceAllocation_Stop:
		HandleDeviceAllocationStop(pEvent);
		break;

	case PagingOpVirtualTransfer:
		HandlePagingOpVirtualTransfer(pEvent);
		break;
	case PagingOpNotifyResidency:
		HandlePagingOpNotifyResidency(pEvent);
		break;
	case PagingOpSysmemCommit:
		HandlePagingOpSysmemCommit(pEvent);
		break;
	case PagingOpSysmemUncommit:
		HandlePagingOpSysmemUncommit(pEvent);
		break;

	default:
		break;
	}
}

void WINAPI EventRecordCallback(PEVENT_RECORD pEvent)
{
	g_traceStarted.store(true, std::memory_order_release);
	if(!pEvent)
		return;

	EnterCriticalSection(&g_critSec);
	struct exitDummy
	{
		~exitDummy()
		{
			LeaveCriticalSection(&g_critSec);
		}
	} foo;

	if(IsEqualGUID(pEvent->EventHeader.ProviderId, KernelProcessGuid))
	{
		HandleProcessEvent(pEvent);
	}
	else if(IsEqualGUID(pEvent->EventHeader.ProviderId, DxgKrnlGuid))
	{
		HandleDxgKrnlEvent(pEvent);
	}
}

void StopTraceSession()
{
	if(g_traceHandle != INVALID_PROCESSTRACE_HANDLE)
	{
		CloseTrace(g_traceHandle);
		g_traceHandle = INVALID_PROCESSTRACE_HANDLE;
	}

	if(g_sessionHandle != 0)
	{
		size_t					bufferSize	= sizeof(EVENT_TRACE_PROPERTIES) + (wcslen(SESSION_NAME) + 1) * sizeof(wchar_t);
		PEVENT_TRACE_PROPERTIES pProperties = (PEVENT_TRACE_PROPERTIES)malloc(bufferSize);
		if(pProperties)
		{
			ZeroMemory(pProperties, bufferSize);
			pProperties->Wnode.BufferSize = (ULONG)bufferSize;
			pProperties->LoggerNameOffset = sizeof(EVENT_TRACE_PROPERTIES);
			ControlTraceW(g_sessionHandle, SESSION_NAME, pProperties, EVENT_TRACE_CONTROL_STOP);
			free(pProperties);
		}
		g_sessionHandle = 0;
	}
}

BOOL WINAPI ConsoleHandler(DWORD ctrlType)
{
	if(ctrlType == CTRL_C_EVENT || ctrlType == CTRL_BREAK_EVENT)
	{
		return TRUE;
	}
	return FALSE;
}

void HideCursor()
{
	CONSOLE_CURSOR_INFO cursorInfo;
	GetConsoleCursorInfo(g_hConsoleOutput, &cursorInfo);
	cursorInfo.bVisible = FALSE;
	SetConsoleCursorInfo(g_hConsoleOutput, &cursorInfo);
}

void ShowCursor()
{
	CONSOLE_CURSOR_INFO cursorInfo;
	GetConsoleCursorInfo(g_hConsoleOutput, &cursorInfo);
	cursorInfo.bVisible = TRUE;
	SetConsoleCursorInfo(g_hConsoleOutput, &cursorInfo);
}

void ClearScreen()
{
	CONSOLE_SCREEN_BUFFER_INFO csbi;
	DWORD					   count;
	DWORD					   cellCount;
	COORD					   homeCoords = { 0, 0 };

	if(!GetConsoleScreenBufferInfo(g_hConsoleOutput, &csbi))
		return;
	cellCount = csbi.dwSize.X * csbi.dwSize.Y;

	FillConsoleOutputCharacter(g_hConsoleOutput, ' ', cellCount, homeCoords, &count);
	FillConsoleOutputAttribute(g_hConsoleOutput, g_originalAttributes, cellCount, homeCoords, &count);
	SetConsoleCursorPosition(g_hConsoleOutput, homeCoords);
}

void RestoreConsole()
{
	ClearScreen();
	SetConsoleTextAttribute(g_hConsoleOutput, g_originalAttributes);
	ShowCursor();
}

void GetConsoleSize(int& width, int& height)
{
	CONSOLE_SCREEN_BUFFER_INFO csbi;
	if(GetConsoleScreenBufferInfo(g_hConsoleOutput, &csbi))
	{
		width  = csbi.srWindow.Right - csbi.srWindow.Left + 1;
		height = csbi.srWindow.Bottom - csbi.srWindow.Top + 1;
	}
	else
	{
		width  = 80;
		height = 25;
	}
}

void FormatMemory(SIZE_T bytes, char* buffer, size_t bufSize)
{
	double b = (double)bytes;
	int	   x = 0;
	for(int i = 0; i < g_minSize; ++i)
	{
		b /= 1024.f;
		x++;
	}
	const char ext[] = { ' ', 'K', 'M', 'G', 'T' };

	while(b > 1024 && x + 1 < _countof(ext))
	{
		b /= 1024.f;
		x++;
	}
	sprintf_s(buffer, bufSize, "%6.1f %cB", b, ext[x]);
}

static void NextLine()
{
	g_currentX = 0;
	g_currentY++;
}

static void Put(char c)
{
	if(g_currentX < g_consoleWidth)
	{
		int idx = g_currentY * g_consoleWidth + g_currentX;
		if(idx < g_chars.size())
		{
			g_chars.at(idx).Char.AsciiChar = c;
			g_chars.at(idx).Attributes	   = (WORD)g_currentColor;
		}
		g_currentX += 1;
	}
}

template <typename... Args>
static void PutFormat(const char* fmt, Args&&... args) /// wtf is going on with c++
{
	char buffer[512];
	int	 r = std::snprintf(buffer, sizeof(buffer), fmt, std::forward<decltype(args)>(args)...);
	if(r > 0)
	{
		int base = g_currentY * g_consoleWidth;
		int i	 = 0;
		while(i < r && g_currentX < g_consoleWidth)
		{
			int idx = base + g_currentX;
			if(idx < g_chars.size())
			{
				g_chars.at(idx).Char.AsciiChar = buffer[i];
				g_chars.at(idx).Attributes	   = (WORD)g_currentColor;
			}
			g_currentX += 1;
			i++;
		}
	}
}

void DrawMemoryBar(const ProcessMemory* process, SIZE_T maxMemoryBytes, int barWidth)
{
	SIZE_T usage	   = process->UsageLocal;
	double barBytes	   = (double)maxMemoryBytes / (double)barWidth;
	double rcpBarBytes = (double)barWidth / (double)maxMemoryBytes;

	int filledBars = (int)(usage / barBytes);
	if(filledBars > barWidth)
		filledBars = barWidth;
	if(usage > 0 && filledBars == 0)
		filledBars = 1;

	double floatBarPos = 0;
	int	   barPut	   = 0;
	int	   idx		   = 0;
	int	   bars[PRIO_COUNT];
	for(int i = PRIO_COUNT - 1; i >= 0; --i)
	{
		UINT64 dem = process->CommitmentDemoted[i];
		if(!dem)
			bars[i] = 0;
		else
		{
			double newFloatBarPos = floatBarPos + (dem * rcpBarBytes);
			int	   c			  = (int)ceil(newFloatBarPos);
			bars[i]				  = c - barPut;
			if(bars[i])
				barPut = c;
			floatBarPos = newFloatBarPos;
		}
	}
	int tail	   = barWidth - filledBars;
	int baseBars   = filledBars - barPut;
	g_currentColor = WHITE;
	Put('[');
	g_currentColor = (GREEN);
	for(int i = 0; i < baseBars; i++)
		Put('#');

	for(int i = 0; i < PRIO_COUNT; ++i)
	{
		int count = bars[i];
		if(count)
		{
			g_currentColor = (g_PrioTocolor[i + 1]);
			for(int j = 0; j < count; ++j)
			{
				Put('#');
			}
		}
	}

	for(int i = 0; i < tail; i++)
	{
		g_currentColor = (DARK_GRAY);
		Put('-');
	}

	g_currentColor = (WHITE);
	Put(']');
}

void ConsoleUpdate()
{
	EnterCriticalSection(&g_critSec);
	struct exitDummy
	{
		~exitDummy()
		{
			LeaveCriticalSection(&g_critSec);
		}
	} foo;

	static std::vector<ProcessMemory*> processes;
	static std::vector<PVOID>		   adapters;

	processes.clear();
	adapters.clear();

	UINT64 maxUsage = 1;
	for(auto& pair : g_processMemory)
	{
		ProcessMemory& mem	   = (pair).second;
		PVOID		   adapter = pair.first.pDxgAdapter;
		mem.pid				   = pair.first.pid;
		mem.pDxgAdapter		   = adapter;
		processes.push_back(&mem);
		maxUsage = mem.UsageLocal > maxUsage ? mem.UsageLocal : maxUsage;
	}
	std::sort(processes.begin(),
			  processes.end(),
			  [](const ProcessMemory* a, const ProcessMemory* b)

			  {
				  bool aTracked = a->isTracked;
				  bool bTracked = b->isTracked;
				  if(aTracked == bTracked)
					  return a->UsageLocal > b->UsageLocal;
				  else
					  return (aTracked > bTracked);
			  });

	GetConsoleSize(g_consoleWidth, g_consoleHeight);

	if(g_consoleWidth != g_lastWidth || g_consoleHeight != g_lastHeight)
	{
		ClearScreen();
		g_lastWidth	 = g_consoleWidth;
		g_lastHeight = g_consoleHeight;
	}

	const int HEADER_LINES = 4;
	int		  maxProcesses = g_consoleHeight - HEADER_LINES;
	if(maxProcesses < 1)
		maxProcesses = 1;

	int displayCount = std::min(maxProcesses, (int)processes.size());

	for(int i = 0; i < displayCount; i++)
	{
		PVOID adapter = processes[i]->pDxgAdapter;
		if(adapters.end() == std::find(adapters.begin(), adapters.end(), adapter))
			adapters.push_back(adapter);
	}

	int nameWidth	= 25;
	int memoryWidth = 10;

	if(g_consoleWidth < 60)
	{
		nameWidth = 15;
	}

	bool showDetailed = false;

	int fixedWidth		= nameWidth + 3 * (1 + memoryWidth) - 1;
	int fixedWidthAll	= nameWidth + (3 + 4) * (1 + memoryWidth) - 1;
	g_detailedAvailable = fixedWidthAll + 15 < g_consoleWidth;
	if(g_detailedAvailable && g_detailedMode)
	{
		showDetailed = true;
		fixedWidth	 = fixedWidthAll;
	}

	int barWidth = g_consoleWidth - fixedWidth;

	if(barWidth < 10)
		barWidth = 10;

	int numProcesses = (int)processes.size();

	g_currentX	   = 0;
	g_currentY	   = 0;
	g_currentColor = WHITE;

	auto GetAdapterColor = [&](PVOID adapter)
	{
		for(int i = 0; i < adapters.size(); ++i)
		{
			if(adapters[i] == adapter)
			{
				return g_adapterToColor[i % g_numAdapterColors];
			}
		}
		return (int)WHITE;
	};

	g_chars.resize(g_consoleWidth * g_consoleHeight);
	for(CHAR_INFO& c : g_chars)
	{
		c.Char.AsciiChar = ' ';
		c.Attributes	 = 0;
	}

	int colorIndex = 0;
	int pos		   = 0;
	for(PVOID adapter : adapters)
	{
		g_currentColor = GetAdapterColor(adapter);
		Adapter* a	   = FindAdapter(adapter);
		PutFormat("[%ls (%.1fGB)] ", a->name.c_str(), a->LocalMemory / (1024.0 * 1024.0 * 1024.0));
	}
	NextLine();
	auto WritePrios = []()
	{
		PutFormat("[");
		for(int i = 0; i < 5; ++i)
		{
			g_currentColor = g_PrioTocolor[i + 1];
			if(i != 4)
				PutFormat("%s ", g_prioNames[i + 1]);
			else
			{
				PutFormat("%s", g_prioNames[i + 1]);
				g_currentColor = (CYAN);
				Put(']');
			}
		}
	};

	g_currentColor = CYAN;
	PutFormat("%-*s  %*s  %*s  ", nameWidth, "Process Name", memoryWidth - 1, "Usage", memoryWidth - 1, "Commit");
	PutFormat("%*s  ", memoryWidth - 1, "Demoted");
	if(showDetailed)
	{
		WritePrios();
		int lim = g_consoleWidth - barWidth;
		while(g_currentX++ < lim + 2)
			;
	}
	g_currentColor = GREEN;
	PutFormat("Present ");
	g_currentColor = CYAN;
	PutFormat("Demoted");
	WritePrios();
	NextLine();

	g_currentColor = DARK_GRAY;
	for(int i = 0; i < g_consoleWidth; i++)
		Put('-');
	NextLine();
	for(int i = 0; i < maxProcesses; i++)
	{
		if(i < displayCount)
		{
			const ProcessMemory* procMem = processes[i];
			if(procMem->CommitmentLocal == 0 && procMem->UsageLocal == 0)
				continue;
			Process* proc = FindProcess(procMem->pid);
			if(proc->imageFilename.length() == 0)
			{
				proc->imagePath		= GetProcessName(procMem->pid);
				proc->imageFilename = GetFileName(proc->imagePath);
				proc->isTracked		= ProcessCheckTracked(proc->imagePath);
			}
			char nameBuffer[64] = {};
			if(proc->isTracked)
			{
				nameBuffer[0] = '*';
				WideCharToMultiByte(CP_ACP, 0, proc->imageFilename.c_str(), -1, nameBuffer + 1, sizeof(nameBuffer) - 2, NULL, NULL);
			}
			else
				WideCharToMultiByte(CP_ACP, 0, proc->imageFilename.c_str(), -1, nameBuffer, sizeof(nameBuffer) - 1, NULL, NULL);

			// Truncate if needed
			if((int)strlen(nameBuffer) > nameWidth - 1)
			{
				nameBuffer[nameWidth - 4] = '.';
				nameBuffer[nameWidth - 3] = '.';
				nameBuffer[nameWidth - 2] = '.';
				nameBuffer[nameWidth - 1] = '\0';
			}

			g_currentColor = GetAdapterColor(procMem->pDxgAdapter);
			PutFormat("%-*s", nameWidth, nameBuffer);

			char memBuffer[32];
			FormatMemory(procMem->UsageLocal, memBuffer, sizeof(memBuffer));
			g_currentColor = CYAN;
			PutFormat(" %*s", memoryWidth, memBuffer);

			FormatMemory(procMem->CommitmentLocal, memBuffer, sizeof(memBuffer));
			g_currentColor = CYAN;
			PutFormat(" %*s", memoryWidth, memBuffer);

			if(showDetailed)
			{
				int idx = 0;
				for(UINT64 dem : procMem->CommitmentDemoted)
				{
					FormatMemory(dem, memBuffer, sizeof(memBuffer));
					if(dem)
					{
						g_currentColor = (g_PrioTocolor[idx + 1]);
					}
					else
					{
						g_currentColor = DARK_GRAY;
					}
					PutFormat(" %*s", memoryWidth, memBuffer);
					idx++;
				}
			}
			else
			{
				UINT64 DemotedSum	  = 0;
				int	   prioColorIndex = 0;
				int	   idx			  = 0;
				for(UINT64 dem : procMem->CommitmentDemoted)
				{
					if(dem)
						prioColorIndex = idx + 1;
					DemotedSum += dem;
					idx++;
				}

				FormatMemory(DemotedSum, memBuffer, sizeof(memBuffer));
				g_currentColor = (g_PrioTocolor[prioColorIndex]);
				PutFormat(" %*s", memoryWidth, memBuffer);
			}
			Put(' ');
			DrawMemoryBar(procMem, maxUsage, barWidth - 5);
			g_currentColor = (WHITE);
		}

		for(int j = g_currentX; j < g_consoleWidth; j++)
			Put(' ');

		NextLine();
	}
	g_currentColor = (DARK_GRAY);
	g_currentY	   = g_consoleHeight - 1;

	PutFormat("Refreshing... [Esc:exit");
	if(g_detailedAvailable)
		PutFormat(" Space:detailed ");

	PutFormat(" bmkg:bytes]");

	for(int i = g_currentX; i < g_consoleWidth - 1; i++)
		Put(' ');
	SMALL_RECT r{ 0, 0, (SHORT)g_consoleWidth, (SHORT)g_consoleHeight };
	WriteConsoleOutputA(g_hConsoleOutput, &g_chars[0], { (SHORT)g_consoleWidth, (SHORT)g_consoleHeight }, { 0, 0 }, &r);
	g_currentColor = (WHITE);
}

void ParseCommandLine()
{
	int		argc  = 0;
	LPWSTR* argv  = CommandLineToArgvW(GetCommandLineW(), &argc);
	bool	found = false;
	for(int i = 1; i < argc; ++i)
	{
		if(lstrcmpiW(argv[i], L"-v") == 0 || lstrcmpiW(argv[i], L"--verbose") == 0)
		{
			g_verbose = true;
			break;
		}
		else if(argv[i][0] != L'-')
		{
			g_trackedProcesses.push_back(argv[i]);
		}
	}
}
int WINAPI WinMain(HINSTANCE, HINSTANCE, LPSTR, int)
{
	ParseCommandLine();
	fopen_s(&g_LogFile, "demote_tracker_log.txt", "w");

	g_hRedrawEvent = CreateEvent(NULL, FALSE, FALSE, L"ConsoleRedrawEvent");

	struct exitDummy
	{
		~exitDummy()
		{
			fclose(g_LogFile);
		}
	} foo;

	AllocConsole();

	g_hConsoleInput	 = CreateFileA("CONIN$", GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, 0, NULL);
	g_hConsoleOutput = CreateFileA("CONOUT$", GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, 0, NULL);
	SetConsoleOutputCP(CP_UTF8);
	SetConsoleCP(CP_UTF8);

	InitializeCriticalSection(&g_critSec);

	{
		size_t					bufferSize	= sizeof(EVENT_TRACE_PROPERTIES) + (wcslen(SESSION_NAME) + 1) * sizeof(wchar_t);
		PEVENT_TRACE_PROPERTIES pProperties = (PEVENT_TRACE_PROPERTIES)malloc(bufferSize);
		if(pProperties)
		{
			ZeroMemory(pProperties, bufferSize);
			pProperties->Wnode.BufferSize = (ULONG)bufferSize;
			pProperties->LoggerNameOffset = sizeof(EVENT_TRACE_PROPERTIES);
			ControlTraceW(0, SESSION_NAME, pProperties, EVENT_TRACE_CONTROL_STOP);
			free(pProperties);
		}
	}

	size_t					bufferSize		   = sizeof(EVENT_TRACE_PROPERTIES) + (wcslen(SESSION_NAME) + 1) * sizeof(wchar_t);
	PEVENT_TRACE_PROPERTIES pSessionProperties = (PEVENT_TRACE_PROPERTIES)malloc(bufferSize);
	if(!pSessionProperties)
	{
		wprintf(L"Failed to allocate memory for trace properties.\n");
		return 1;
	}

	ZeroMemory(pSessionProperties, bufferSize);
	pSessionProperties->Wnode.BufferSize	= (ULONG)bufferSize;
	pSessionProperties->Wnode.Flags			= WNODE_FLAG_TRACED_GUID;
	pSessionProperties->Wnode.ClientContext = 1;
	pSessionProperties->LogFileMode			= EVENT_TRACE_REAL_TIME_MODE;
	pSessionProperties->LoggerNameOffset	= sizeof(EVENT_TRACE_PROPERTIES);

	ULONG status = StartTraceW(&g_sessionHandle, SESSION_NAME, pSessionProperties);
	if(status != ERROR_SUCCESS)
	{
		wprintf(L"Failed to start trace session. Error: %lu\n", status);
		if(status == ERROR_ACCESS_DENIED)
		{
			wprintf(L"Please run as Administrator.\n");
		}
		free(pSessionProperties);
		return 1;
	}

	ENABLE_TRACE_PARAMETERS kernelProcessParams = {};
	kernelProcessParams.Version					= ENABLE_TRACE_PARAMETERS_VERSION_2;
	kernelProcessParams.EnableProperty			= EVENT_ENABLE_PROPERTY_PROCESS_START_KEY;

	status = EnableTraceEx2(g_sessionHandle, &KernelProcessGuid, EVENT_CONTROL_CODE_ENABLE_PROVIDER, TRACE_LEVEL_VERBOSE, 0x10 | 0x20, 0, 0, &kernelProcessParams);

	if(status != ERROR_SUCCESS)
	{
		wprintf(L"Warning: Failed to enable Kernel-Process provider. Error: %lu\n", status);
		wprintf(L"Process start/stop detection will not work.\n");
		fflush(stdout);
		// Continue anyway - we can still track if process is already running
	}
	EVENT_TRACE_LOGFILEW logfile = { 0 };
	logfile.LoggerName			 = (LPWSTR)SESSION_NAME;
	logfile.ProcessTraceMode	 = PROCESS_TRACE_MODE_REAL_TIME | PROCESS_TRACE_MODE_EVENT_RECORD;
	logfile.EventRecordCallback	 = EventRecordCallback;

	g_traceHandle = OpenTraceW(&logfile);
	if(g_traceHandle == INVALID_PROCESSTRACE_HANDLE)
	{
		wprintf(L"Failed to open trace. Error: %lu\n", GetLastError());
		StopTraceSession();
		free(pSessionProperties);
		return 1;
	}

	std::thread traceThread(
		[]()
		{
			ULONG traceStatus = ProcessTrace(&g_traceHandle, 1, nullptr, nullptr);
			if(traceStatus != ERROR_SUCCESS && traceStatus != ERROR_CANCELLED)
			{
				wprintf(L"ProcessTrace failed. Error: %lu\n", traceStatus);
			}
		});

	for(int i = 0; i < 100 && !g_traceStarted.load(std::memory_order_acquire); i++)
	{
		Sleep(10);
	}

	status = EnableTraceEx2(g_sessionHandle, &KernelProcessGuid, EVENT_CONTROL_CODE_CAPTURE_STATE, TRACE_LEVEL_VERBOSE, 0x10 | 0x20, 0, INFINITE, &kernelProcessParams);
	if(status != ERROR_SUCCESS)
	{
		wprintf(L"Warning: Failed to request Kernel-Process capture state. Error: %lu\n", status);
		wprintf(L"Existing processes will not be enumerated.\n");
		fflush(stdout);
	}

	status = EnableTraceEx2(g_sessionHandle,
							&DxgKrnlGuid,
							EVENT_CONTROL_CODE_ENABLE_PROVIDER,
							TRACE_LEVEL_VERBOSE,
							0xFFFFFFFFFFFFFFFF, // All keywords including Resource, Memory, References
							0,
							0,
							nullptr);

	if(status != ERROR_SUCCESS)
	{
		wprintf(L"Failed to enable DxgKrnl provider. Error: %lu\n", status);
		StopTraceSession();
		free(pSessionProperties);
		return 1;
	}

	status = EnableTraceEx2(g_sessionHandle, &DxgKrnlGuid, EVENT_CONTROL_CODE_CAPTURE_STATE, TRACE_LEVEL_VERBOSE, 0xFFFFFFFFFFFFFFFF, 0, INFINITE, nullptr);
	if(status != ERROR_SUCCESS)
	{
		wprintf(L"Warning: Failed to request Kernel-Process capture state. Error: %lu\n", status);
		wprintf(L"Existing processes will not be enumerated.\n");
		fflush(stdout);
	}
	else
	{
		wprintf(L"Capture state requested successfully.\n");
		fflush(stdout);
	}

	CONSOLE_SCREEN_BUFFER_INFO csbi;
	if(GetConsoleScreenBufferInfo(g_hConsoleOutput, &csbi))
	{
		g_originalAttributes = csbi.wAttributes;
	}
	SetConsoleCtrlHandler(ConsoleHandler, TRUE);

	SetConsoleTitleW(L"Demote Tracker");

	HideCursor();
	ClearScreen();

	while(1)
	{
		do
		{
			INPUT_RECORD Record, Record0;
			DWORD		 Length;

			auto r = PeekConsoleInput(g_hConsoleInput, &Record, 1, &Length);
			if(!r || Length == 0)
				break;
			ReadConsoleInput(g_hConsoleInput, &Record, 1, &Length);
			WORD ch = Record.Event.KeyEvent.wVirtualKeyCode;
			if(Record.Event.KeyEvent.bKeyDown && ch != 0)
			{
				if(ch == 'G')
				{
					g_minSize = g_minSize == 3 ? 0 : 3;
				}
				else if(ch == 'M')
				{
					g_minSize = g_minSize == 2 ? 0 : 2;
				}
				else if(ch == 'K')
				{
					g_minSize = g_minSize == 1 ? 0 : 1;
				}
				else if(ch == 'B')
				{
					g_minSize = 0;
				}
				else if(ch == 0x20)
				{
					g_detailedMode = !g_detailedMode;
				}
				if(ch == 27)
				{
					StopTraceSession();
					wprintf(L"\nStopping trace...\n");
					fflush(stdout);
				}
			}

		} while(1);
		if(g_sessionHandle == 0)
		{
			wprintf(L"Exit detected.\n");
			fflush(stdout);
			break;
		}
		ConsoleUpdate();
		HANDLE handles[] = { g_hRedrawEvent, g_hConsoleInput };
		WaitForMultipleObjects(2, handles, FALSE, 1000);
		Sleep(4000);
	}

	traceThread.join();

	StopTraceSession();

	FreeConsole();

	free(pSessionProperties);

	return 0;
}

static void dprintf(LPVOID pid, const char* fmt, ...)
{
	if(0 != pid && !FindProcess((DWORD)(INT64)pid)->isTracked)
	{
		return;
	}

	char buffer[4096];

	va_list args;
	va_start(args, fmt);
	int len = vsnprintf(buffer, sizeof(buffer), fmt, args);
	va_end(args);

	if(len < 0)
		return;

	// Ensure null-termination even if truncated
	buffer[sizeof(buffer) - 1] = '\0';

	OutputDebugStringA(buffer);
}
