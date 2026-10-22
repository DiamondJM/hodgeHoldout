#!/bin/sh
cd /home/user/hodgeHoldout/sweep
xargs -P3 -I{} sh -c 'python3 fixed_d.py /home/user/sextics/data {} > logs/{}.log 2>&1' < instances.txt
