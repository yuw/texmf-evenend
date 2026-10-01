#!/bin/sh
# 固定のテスト一式：fuzz（本文の長さを変える），fuzzswitch（段数の切り換え，図あり／なし），
# fnfloat（同じ段のフロートと脚注），gyoudori（行ドリとの組み合わせ48通り）．
# TeX Liveの版は環境変数TLYEAR（既定は2026）
cd "$(dirname "$0")"
echo "== fuzz"; STEP=9 ./fuzz.sh 1 140 | grep -v "err=0"; STEP=13 ./fuzz.sh 1 140 footnote=column | grep -v "err=0"; STEP=13 ./fuzz.sh 1 140 columns=3 3 | grep -v "err=0"
echo "== fuzzswitch fig"; FIG=1 ./fuzzswitch.sh | awk '{print $2,$3,$NF}' | sort | uniq -c
echo "== fuzzswitch nofig"; FIG=0 ./fuzzswitch.sh | awk '{print $2,$3,$4,$NF}' | sort | uniq -c
echo "== fnfloat (not ok count)"; ./fnfloat.sh 2>&1 | grep -vc "err=0 overfull=0 blocks: [0-9], problems: 0 | problems: 0"
echo "== gyoudori"; ./gy/sweep.sh 2>&1 | tail -5
