#!/bin/sh
# resumable: each instance skips candidates already in logs/<id>.log (cycle-q2 excluded: dense q=2 system exceeds memory)
cd /home/user/hodgeHoldout/sweep
xargs -P3 -I{} sh -c 'python3 fixed_d.py /home/user/sextics/data {} >> logs/{}.log 2>&1' < instances_q1.txt
