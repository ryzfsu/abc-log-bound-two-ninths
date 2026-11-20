# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
976781 (2026-11-20 20:28:03 UTC).

| file | SHA-256 |
|---|---|
| `abc-log-bound-two-ninths-v1.pdf` | `701cca02bfae5c91299a2c1120307217c4157aa3cf06df31b5f08302ea7c37d1` |
| `abc-log-bound-two-ninths-v1.tar.gz` | `f84a9c3a52fa818426adf8190ca182b9946055fe6331633a02895c904e71a979` |
| `abc-log-bound-two-ninths-v1-lean.tar.gz` | `ed1c5fe1baee7d9473cd864e4115645f40ec97599a453d5cd7b5cd04fbfab975` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
