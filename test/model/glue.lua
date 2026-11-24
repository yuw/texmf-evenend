-- 高さを指定して組む箱のグルーの割り振り：TeX（node.vpack）の実測を，lean/Glue.leanのモデルの
-- 期待値（lean/expect/GridGlue.txt）と比べる．evenendは通さない
local HLIST = node.id('hlist')
local function frac(s)
  local a, b = s:match('^(-?%d+)/(%d+)$')
  if a then return a / b end
  return tonumber(s)
end
local n, bad = 0, 0
for line in io.lines(os.getenv('EXPECT') .. '/GridGlue.txt') do
  local spec, target, want = line:match('^(.-) | (.-) | (.-)$')
  local head, tail, nodes = nil, nil, {}
  for item in spec:gmatch('%S+') do
    local q
    if item:sub(1, 1) == 'b' then
      q = node.new('hlist'); q.height = math.floor(frac(item:sub(2)) * 65536 + 0.5)
    else
      local w, st, sh, fil = item:match('^g(.-),(.-),(.-),(.-)$')
      q = node.new('glue')
      node.setglue(q, frac(w) * 65536, frac(st) * 65536, frac(sh) * 65536, fil == '1' and 1 or 0, 0)
    end
    if tail then tail.next = q; q.prev = tail else head = q end
    tail = q; nodes[#nodes + 1] = q
  end
  local b = node.vpack(head, math.floor(frac(target) * 65536 + 0.5), 'exactly')
  local i, ok, gots = 0, true, {}
  for w in want:gmatch('%S+') do
    i = i + 1
    local q, got = nodes[i], nil
    if q.id == HLIST then got = q.height
    else
      got = q.width
      if b.glue_sign == 1 and q.stretch_order == b.glue_order then
        got = got + b.glue_set * q.stretch
      elseif b.glue_sign == 2 and q.shrink_order == b.glue_order then
        got = got - b.glue_set * q.shrink
      end
    end
    gots[i] = string.format('%.4f', got / 65536)
    if math.abs(got / 65536 - frac(w)) > 0.001 then ok = false end
  end
  n = n + 1
  if not ok then
    bad = bad + 1
    if bad <= 10 then texio.write_nl('log', 'DIFF ' .. line .. ' | TeX: ' .. table.concat(gots, ' ')) end
  end
  node.flush_list(b)
end
texio.write_nl('log', string.format('RESULT glue: %d cases, %d differ', n, bad))
