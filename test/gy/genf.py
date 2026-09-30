# gyoudoriとの組み合わせのテスト文書を作る．使い方: genf.py クラス オプション 段数(1|2) 出力.tex
# オプション：gyoudoriのオプションに加えて，n=段落数，ee=evenendのオプション（+で区切る），
# fe=flushendのオプション，fn（脚注），st（stfloats），dblb（段抜きの下のフロート），tab（段抜きを表に），
# displaymath（別行数式），clear（\clearpage直前の下のフロート），nidan／nidanfirst（nidanfloat），fnbelow
# 目印：\M{名前}の位置をPOS行としてログに書く（P*：本文の段落，Q*：数式の後，FIG-位置-高さ：フロート）
import sys
cls, opts, twocol = sys.argv[1], sys.argv[2], sys.argv[3]=='2'
para = "本文の段落です．" * 12
out = [r"\documentclass%s{%s}" % ("[twocolumn]" if twocol else "", cls),
       (r"\usepackage{nidanfloat}" if "nidanfirst" in opts else "") +
       r"\usepackage[%s]{gyoudori}" % ",".join(o for o in opts.split(",") if o not in ("clear","nidan","nidanfirst","dblb","st","fnbelow","fn","tab") and not o.startswith(("fe=","n=","ee="))) +
       (r"\usepackage{nidanfloat}" if "nidan" in opts.split(",") else "") +
       (r"\usepackage{stfloats}" if "st" in opts.split(",") else "") +
       (r"\fnbelowfloat" if "fnbelow" in opts.split(",") else "") +
       "".join(r"\usepackage[%s]{flushend}" % o[3:].replace("+",",") for o in opts.split(",") if o.startswith("fe=")) +
       ("\\usepackage{amsmath}" if "displaymath" in opts else "") +
       "".join(r"\usepackage[%s]{evenend}" % o[3:].replace("+",",") for o in opts.split(",") if o.startswith("ee=")),
       r"\ifdefined\savepos\let\pdfsavepos\savepos\let\pdflastypos\lastypos\let\pdflastxpos\lastxpos\fi",
       r"""\newcount\L
\makeatletter
\def\M#1{\leavevmode\global\advance\L1 \pdfsavepos
  \edef\x{\noexpand\write-1{POS \the\L\space #1 \noexpand\the\pdflastypos\space\noexpand\thepage\space\noexpand\the\pdflastxpos}}\x}
% フロートの中身：高さ#2ptの罫．下端（ベースライン）を記録
\def\F#1#2{\begin{figure}[#1]\centering\rule{3cm}{#2pt}\M{FIG-#1-#2}\end{figure}}
\def\FF#1#2{\begin{DBLENV}[#1]\centering\rule{3cm}{#2pt}\M{FIG-#1-#2}\end{DBLENV}}
\makeatother
\begin{document}""".replace("DBLENV", "table*" if "tab" in opts.split(",") else "figure*")]
floats = [("t",40),("b",23),("h",31),("t",61),("h",12),("b",70),("t",25),("t",33),("h",50),("b",18),("b",44),("h",27)]
npara = int(([o[2:] for o in opts.split(",") if o.startswith("n=")] or ["40"])[0])
for i in range(npara):
    out.append(r"\M{P%d}%s" % (i, para) + (r"脚注\footnote{脚注の本文です．脚注の本文です．}" if "fn" in opts.split(",") and i % 7 == 2 else ""))
    if i % 3 == 1 and floats:
        p,h = floats.pop(0)
        out.append(r"\F{%s}{%d}" % (p,h))
    if twocol and i in (5, 20):
        out.append(r"\FF{t}{%d}" % (45 if i==5 else 28))
    if twocol and "dblb" in opts and i in (8, 23, 30):
        out.append(r"\FF{b}{%d}" % {8:52, 23:21, 30:37}[i])
    if i == 14 and "clear" in opts: out.append(r"\F{b}{36}\clearpage")
    if "displaymath" in opts and i % 5 == 3: out.append(r"\begin{align}a&=b\\c&=d\end{align}\M{Q%d}続き．" % i)
    out.append("")
out.append(r"\end{document}")
open(sys.argv[4],'w').write("\n".join(out))
