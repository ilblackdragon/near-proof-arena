# YieldCongestion: nearcore outcomes per step (5 runs)

| step | nearcore (first receipt; later failures) × runs |
|---|---|
| `00.create-resumed-cross-shard-buffered` | createdQ; cb:01 buffered +106Q ×1; created; cb:01 buffered +41Q ×1; created; cb:01 buffered +37Q ×1; created; cb:01 buffered +36Q ×1; created; cb:01 buffered +43Q ×1 |
| `01.create-timeout-under-congestion` | createdQ; callback pending at run end ×1; created; cb:02 +236 ×1; created; cb:02 +237 ×1; created; cb:02 +245 ×1; created; cb:02 +234 ×1 |
| `02.create-timeout-under-congestion-note` | createdQ; callback pending at run end ×1; created; cb:02 +236 ×1; created; cb:02 +237 ×1; created; cb:02 +245 ×1; created; cb:02 +234 ×1 |
| `03.create-resumed-locally-under-congestion` | createdQ; cb:01 under-congestion +35Q ×1; created; cb:01 under-congestion +23Q ×1; created; cb:01 under-congestion +21Q ×1; created; cb:01 under-congestion +19Q ×1; created; cb:01 under-congestion +25Q ×1 |
| `04.create-resumed-after-own-shard-flood` | created; cb:01 flood +26Q ×2; createdQ; cb:01 flood +46Q ×1; created; cb:01 flood +27Q ×1; created; cb:01 flood +31Q ×1 |
| `05.create-resumed-cross-shard-small` | created; cb:01 cross-small +43Q ×2; createdQ; cb:01 cross-small +118Q ×1; created; cb:01 cross-small +40Q ×1; created; cb:01 cross-small +39Q ×1 |
| `06.create-resume-races-deferred-timeout` | created; cb:01 late-but-first +224Q ×2; createdQ; callback pending at run end ×1; created; cb:01 late-but-first +226Q ×1; created; cb:01 late-but-first +229Q ×1 |
| `07.resume-local-under-congestion` | ret 01Q ×5 |
| `08.create-under-congestion` | createdQ; callback pending at run end ×1; createdQ; cb:01 created-under-congestion +21Q ×1; createdQ; cb:01 created-under-congestion +31Q ×1; createdQ; cb:01 created-under-congestion +23Q ×1; createdQ; cb:01 created-under-congestion +25Q ×1 |
| `09.resume-cross-shard-buffered` | ret 01Q ×5 |
| `10.resume-after-own-shard-flood` | ret 01Q ×5 |
| `11.resume-created-under-congestion` | ret 01Q ×4; ret 02Q ×1 |
| `12.resume-cross-shard-small` | ret 01Q ×5 |
| `13.create-cross-shard-under-congestion-note` | createdQ; callback pending at run end ×1; createdQ; cb:02 +201 ×1; createdQ; cb:02 +203 ×1; createdQ; cb:02 +213 ×1; createdQ; cb:02 +202 ×1 |
| `14.resume-after-deferred-timeout-due` | ret 01Q ×5 |
