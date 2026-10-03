# Live instance: restart test (2026-10-03)

The queue at the time: 4 submissions, each in or after FORMAL_CHECK. The
reference's FORMAL_CHECK (job `85375d40…`) was leased by `live-w1`, which
had a microVM running.

Steps:

* 15:07:39Z `systemctl --user restart arena-live-server`. `/healthz` came
  back 200 within 3 s.
* 15:07:42Z `systemctl --user restart arena-live-worker@w1`, killing the job
  mid-run. `ExecStopPost` reaped the worker's Firecracker container.

Raw log: `/data/illia/nearproof-live/logs/restart-test.log`.

From the `audit_events` table:

```
15:07:31  worker  job.leased         FORMAL_CHECK 85375d40… attempt 1   (live-w1)
15:07:52  worker  job.leased         FORMAL_CHECK d56710f1… attempt 1   (restarted live-w1 picks up the next job)
15:17:41  system  job.lease_expired  FORMAL_CHECK 85375d40… attempt 1   previous_worker wrk_32cd… (live-w1)
15:17:41  worker  job.leased         FORMAL_CHECK 85375d40… attempt 2   (live-w2)
15:19:13  worker  job.completed      FORMAL_CHECK 85375d40… attempt 2
```

Outcome:

* The interrupted job was retried automatically once its 600 s lease ran out.
* The submission (`sub_d13f817b…`, `examples/reexec-witness`) went on to
  ADMITTED at formal tier with score 130.039.
* The server restart dropped no jobs. Workers reconnected on their next
  poll.
* No submission needed operator action.
