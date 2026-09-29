#!/usr/bin/env python3
"""柱の検証用の文書を作る．使い方: mk.py クラス 段数 ブロックの並び 出力"""
import sys
cls, n0, blocks, out = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
ja = cls != 'article'
P = (r'吾輩は猫である．名前はまだ無い．どこで生れたかとんと見当がつかぬ．何でも薄暗いじめじめした所でニャーニャー泣いていた事だけは記憶している．'
     if ja else r'Lorem ipsum dolor sit amet, consectetuer adipiscing elit. Ut purus elit, vestibulum ut, placerat ac, adipiscing vitae, felis.')
L = [r'\documentclass[%stwocolumn]{%s}' % ('fontsize=10pt,' if cls == 'jlreq' else '', cls),
     r'\usepackage[debug%s]{evenend}' % ('' if n0 == 2 else ',columns=%d' % n0),
     r'\pagestyle{myheadings}',
     r'\makeatletter\def\@oddhead{HEAD[\rightmark][\leftmark]\hfil}\def\@evenhead{\@oddhead}\makeatother',
     r'\begin{document}']
k = 0
for b in blocks.split(','):
    n, paras = b.split(':')
    L.append(r'\evenendcolumns{%s}' % n)
    for _ in range(int(paras)):
        k += 1
        L.append(r'\markboth{L%d}{R%d}MK%d %s %s\par' % (k, k, k, P, P))
L.append(r'\end{document}')
open(out, 'w').write('\n'.join(L) + '\n')
