-- \vsplitの性質：行，グルー，ペナルティ，カーン，\special，\markの並び（長さ4まで．前に1行，
-- 後ろに2行を付ける）を，5通りの高さで\vsplitし，evenend.luaの検査（MC.split）を通す．
-- 切り出した分は元の並びの先頭の部分，残りは続きから捨てられる要素を除いたもの，捨てるのは
-- 捨てられる要素だけ，新しく入るのは\splittopskipのグルーだけ（lean/Fill.leanのSpec）
local el = {
  L = '\\hbox{\\vrule height8pt depth3pt width1pt}', g = '\\vskip5pt plus2pt ',
  p = '\\penalty0 ', P = '\\penalty-10000 ', k = '\\kern3pt ', s = '\\special{x}',
  m = '\\mark{x}',
}
local keys = { 'L', 'g', 'p', 'P', 'k', 's', 'm' }
local words = { '' }
local from = 1
for _ = 1, 4 do
  local to = #words
  for i = from, to do
    for _, k in ipairs(keys) do words[#words + 1] = words[i] .. k end
  end
  from = to + 1
end
function vsplitcheck(h)
  local c = evenend.modelcheck.split(tex.count['evbox'], h)
  if c then node.flush_list(c) end
end
for i = 2, #words do
  local body = words[i]:gsub('.', el)
  for _, h in ipairs({ 0, 12, 20, 30, 100 }) do
    tex.print('\\setbox\\evboxno\\vbox{' .. el.L .. body .. el.L .. el.L .. '}\\directlua{vsplitcheck('
      .. h * 65536 .. ')}')
  end
end
