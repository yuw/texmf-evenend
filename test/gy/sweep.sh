#!/bin/bash
# gyoudoriのfloatオプションとevenendを組み合わせた一括テスト（48通り）．
# クラス（ltjsarticle，jlreq）×条件（なし，脚注page，脚注column，stfloatsと段抜きの
# 下のフロートと表，別行数式，3段）×段落数4通り．本文の行とフロートが行送りの位置に
# あるか（chk.awk），エラー・Overfullがないかを調べる
cd "$(dirname "$0")"
ok=0; tot=0; bal=0
for cls in ltjsarticle jlreq; do for extra in ",ee=" ",fn,ee=footnote=page" ",fn,ee=footnote=column" ",st,dblb,tab,ee=" ",displaymath,ee=" ",ee=columns=3"; do for n in 26 30 34 38; do
  nn=$n; [ "$extra" = ",ee=columns=3" ] && nn=$((n+12))
  job=sw3_$cls-$nn-$(echo "$extra" | tr '+,=' '___')
  ./runl.sh $cls 2 $job "float,n=$nn$extra" > out/$job.out 2>&1
  tot=$((tot+1))
  og=$(grep -o 'off-grid: [0-9]*' out/$job.out | cut -d' ' -f2); ng=$(grep -c 'NG' out/$job.out); of=$(grep -c 'Overfull \\vbox' out/$job.log); er=$(grep -c '^!' out/$job.log)
  grep -q 'columns balanced' out/$job.log && bal=$((bal+1))
  if [ "$og$ng$of$er" != "0000" ]; then echo "$cls n=$nn [$extra] : offgrid=$og NG=$ng overfull=$of errors=$er $(grep -o 'Could not balance\|not balanced' out/$job.log | head -1)"; else ok=$((ok+1)); fi
done; done; done; echo "clean: $ok / $tot  (evenend balanced pages in $bal runs)"
