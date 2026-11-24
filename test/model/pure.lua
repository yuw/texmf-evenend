-- 実装の純粋な計算（evenend.luaのM.pure）を，モデルの関数の結果（lean/grid/GridPure.leanが
-- 書き出したもの）と，小さな範囲の入力のすべてで比べる
local P = evenend.pure
local n, bad = { enum = 0, better = 0, mis = 0, minh = 0 }, { enum = 0, better = 0, mis = 0, minh = 0 }
local shown = 0
local function diff(kind, line, got)
  bad[kind] = bad[kind] + 1
  shown = shown + 1
  if shown <= 20 then texio.write_nl('log', 'DIFF ' .. line .. ' | 実装: ' .. got) end
end
local kinds = {
  n = {}, d = { deferred = true }, t = { span = 2, pos = 'top' }, b = { span = 2, pos = 'bot' },
}
for line in io.lines(os.getenv('PUREFILE')) do
  local head, spec, want = line:match('^(.-) | (.-) | (.-)$')
  if not head then head, want = line:match('^(.-) | (.-)$'); spec = '' end
  local w = {}
  for x in head:gmatch('%S+') do w[#w + 1] = x end
  local kind = w[1]
  local got
  if kind == 'enum' then
    local N, F = tonumber(w[2]), {}
    for o, k in spec:gmatch('(%d+),(%a)') do
      local f = { orig = tonumber(o), pos = 'top', cantop = true }
      for a, b in pairs(kinds[k]) do f[a] = b end
      F[#F + 1] = f
    end
    local cs = P.assigns(F, N, false)
    local h = 0
    for _, a in ipairs(cs) do
      h = (h * 131 + 1000) % 1000000007
      for j = 1, #F do h = (h * 131 + a[j] + 1) % 1000000007 end
    end
    got = #cs .. ' ' .. h
  elseif kind == 'better' then
    local g, s, bm, bh, m, h = tonumber(w[2]), tonumber(w[3]), tonumber(w[4]), tonumber(w[5]),
      tonumber(w[6]), tonumber(w[7])
    got = P.better(bh, bm, h, m, g, 2 * s) and '1' or '0'
  elseif kind == 'mis' then
    local v, shr, textonly, hastext, content = {}, {}, {}, {}, {}
    for a, b, c, d, e in spec:gmatch('(%d+):(%d+):(%d):(%d):(%d)') do
      local i = #v + 1
      v[i], shr[i] = tonumber(a), tonumber(b)
      textonly[i], hastext[i], content[i] = c == '1', d == '1', e == '1'
    end
    local N = #v
    local r = P.misaligned(N, v, shr, textonly, hastext, content, tonumber(w[2]), tonumber(w[3]))
    got = (r and '1' or '0') .. ' ' .. string.format('%.0f', (P.bottom(N, v, shr, textonly)))
  elseif kind == 'minh' then
    local r = P.min_h(function(h) return spec:sub(h + 1, h + 1) == '1' end,
      tonumber(w[2]), tonumber(w[3]), 1)
    got = r and string.format('%.0f', r) or '-'
  end
  if got then
    n[kind] = n[kind] + 1
    if got ~= want then diff(kind, line, got) end
  end
end
for _, k in ipairs({ 'enum', 'better', 'mis', 'minh' }) do
  texio.write_nl('log', string.format('RESULT pure %s: %d cases, %d differ', k, n[k], bad[k]))
  texio.write_nl('log', '')
end
