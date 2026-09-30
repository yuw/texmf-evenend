# 引数: bs ht dp．基準は全ページの本文行のうち最も上のベースライン（=1行目）
{ y=$4/65536; name=$3; pg=$5 }
name ~ /^[PQ]/ { textpg[pg]=1; textcol[pg, ($6/65536<297.6)?"L":"R"]=1; py[++np]=y; pn[np]=name; pp[np]=pg; if (y>top) top=y }
name ~ /^FIG/ { fig[++nf]=name" "y" "pg" "(($6/65536<297.6)?"L":"R") }
function frac(r){ f=r-int(r+(r>=0?0.5:-0.5)); return f<0?-f:f }
END {
  for (i=1;i<=np;i++) { r=(top-py[i])/bs; if (frac(r)>1e-4) {bad++; printf "  TEXT OFF-GRID %s p%d %.4f lines\n", pn[i], pp[i], r} }
  printf "text marks: %d, off-grid: %d\n", np, bad+0
  for (i=1;i<=nf;i++) {
    split(fig[i],a," "); split(a[1],b,"-"); pos=b[2]; H=b[3]; y=a[2]; pg=a[3]
    if (!(pg in textpg)) { printf "  %-12s p%d (float-only page)\n", a[1], pg; continue }
    if (a[1] !~ /-(45|28|52|21|37)$/ && !((pg SUBSEP a[4]) in textcol)) { printf "  %-12s p%d (float-only column)\n", a[1], pg; continue }
    if (pos=="t") { v=(top+ht)-(y+H); what="top    vs glyph-top   " }
    if (pos=="b") { v=(top-dp)-y;     what="bottom vs glyph-bottom" }
    if (pos=="h") { nn=1; while ((nn-1)*bs+ht+dp < H) nn++; A=(nn-1)*bs+ht+dp; v=(top+ht)-(y+H/2+A/2); what="area   vs glyph-top   " }
    r=v/bs
    if (pos=="h" && frac(r)>1e-4) { vt=(top+ht)-(y+H); if (frac(vt/bs)<=1e-4) { r=vt/bs; what="(moved to top) top vs glyph-top" } }
    printf "  %-12s p%d %s %8.4f lines %s\n", a[1], pg, what, r, (frac(r)>1e-4 ? "<-- NG" : "ok")
  }
}
