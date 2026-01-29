`demote_tracker.exe` is a tiny win32 console utility, which can be used to track gpu memory usage of all processes on a windows machine.

The tool uses `ETW` for Windows, and uses to `VidMmProcessCommitmentChange` and `VidMmProcessDemotedCommitmentChange` to capture memory usage.

![demote_tracker](https://github.com/user-attachments/assets/bce5d628-bb9a-42f2-a2e3-d7627687e3df)


# License
Licensed using [MIT](LICENSE)
