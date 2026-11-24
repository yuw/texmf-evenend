-- 行を積んだときの最終行のベースライン：TeXの実測を，lean/Layout.leanのモデルの期待値
-- （lean/expect/GridLines.txt）と比べる．evenendは通さない．
-- 行の並びを\vboxに組み（行送りのグルーはTeXが入れる），先頭で\vsplitして，残りの箱の高さを見る
-- （残りの先頭には\splittopskipのグルーが入る．箱の高さは最終行のベースラインまで）
local n, bad = 0, 0
function linecheck(want, spec)
  -- 残りの並びを自然な高さで組み直して測る（LuaTeXは，\vsplitの残りの箱の深さを\maxdepthで
  -- 抑え，超えた分を高さに移す．evenendも，並びを組み直して測っている）
  local r = tex.box[0]
  local c = node.vpack(node.copy_list(r.list))
  local got = c.height
  node.flush_list(c)
  n = n + 1
  if got ~= want * 65536 then
    bad = bad + 1
    if bad <= 10 then
      texio.write_nl('log', string.format('DIFF %s | model %d | TeX %.4f', spec, want, got / 65536))
    end
  end
end
function linereport()
  texio.write_nl('log', string.format('RESULT lines: %d cases, %d differ', n, bad))
end
for line in io.lines(os.getenv('EXPECT') .. '/GridLines.txt') do
  local spec, want = line:match('^(.-) | (.-)$')
  local t = { '\\setbox0\\vbox{\\baselineskip12pt \\lineskip1pt \\lineskiplimit0pt \\penalty-10000 ' }
  for h, d in spec:gmatch('(%d+),(%d+)') do
    t[#t + 1] = string.format('\\hbox{\\vrule height%spt depth%spt width1pt}', h, d)
  end
  t[#t + 1] = '}\\splittopskip10pt \\setbox2\\vsplit0 to0pt \\directlua{linecheck(' .. want
    .. ', [[' .. spec .. ']])}'
  tex.print(table.concat(t))
end
tex.print('\\directlua{linereport()}')
