-- evenend.lua: 多段組の最終ページで各段の下端を揃える（evenend.styのLua部）
--
-- Copyright (c) 2026 Yuwsuke Kieda
-- Released under the MIT License (see LICENSE)
--
-- 方針：
--   各段の出力時（\@makecol直前）に，段の生の材料（\box255），そこで捨てられる
--   改段位置のグルー類，脚注（\box\footins），段内フロートの複製をとっておく．
--   最終ページの最後の段が出力されるとき，そのページの全段の材料を1本の
--   垂直リストに繋ぎ直し，下端が揃う最小の段の高さを探して\vsplitで再分割する．
--   脚注は属性で本文中の参照位置と結び付けておき，参照位置の移った段へ移す．

local M = {}
evenend = M

local nodeid      = node.id
local GLUE        = nodeid('glue')
local KERN        = nodeid('kern')
local PENALTY     = nodeid('penalty')
local HLIST       = nodeid('hlist')
local VLIST       = nodeid('vlist')
local WHATSIT     = nodeid('whatsit')
local GLYPH       = nodeid('glyph')
local RULE        = nodeid('rule')
local USERDEF     = node.subtype('user_defined')
local TOPSKIP     = 10   -- glueのsubtype：\topskip
local USER_ID     = 0x65766E64  -- 'evnd'

local copy_list   = node.copy_list
local flush_list  = node.flush_list
local vpack       = node.vpack
local has_attr    = node.has_attribute

-- 本文中のフロート（[h]）の印
local INTEXT = luatexbase.new_attribute('evenend@intext')
-- 段をまたぐフロート：またがる段数（置かれた段の箱）と，右の段の場所取りの箱
local SPAN = luatexbase.new_attribute('evenend@span')
local PH = luatexbase.new_attribute('evenend@ph')
local FPS = luatexbase.new_attribute('evenend@fps')

M.cols    = {}   -- 現在のページの段ごとの取り込み
M.fncount = 0
M.curfn   = 0
M.debug   = false

local function info(fmt, ...)
  if M.debug then
    texio.write_nl('log', 'evenend: ' .. string.format(fmt, ...))
  end
end

local function pt(sp) return string.format('%.2fpt', sp / 65536) end

local function is_discardable(n)
  local id = n.id
  return id == GLUE or id == KERN or id == PENALTY
end

-- 連結リストを組み立てる小道具
local function newlist() return { head = nil, tail = nil } end

local function append(l, n)
  if not n then return end
  if l.tail then
    l.tail.next = n
    n.prev = l.tail
  else
    l.head = n
    n.prev = nil
  end
  l.tail = node.tail(n)
end

local function mkglue(w, st, sh, sto, sho)
  local g = node.new(GLUE)
  node.setglue(g, w or 0, st or 0, sh or 0, sto or 0, sho or 0)
  return g
end

local function regglue(r)
  return mkglue(tex.getglue(r))
end

local function filglue()  return mkglue(0, 65536, 0, 1, 0) end
local function vssglue()  return mkglue(0, 65536, 65536, 1, 1) end

-- 垂直リストの自然な高さと深さ（リストは壊さない）
local function natural(head)
  if not head then return 0, 0 end
  local b = vpack(head)
  local h, d = b.height, b.depth
  b.list = nil
  node.free(b)
  return h, d
end

-- 垂直の箱の基準線より下に見かけの上で出る分（中身のはみ出しを含む）
local function vbox_over(t)
  local y, maxb = 0, t.height + t.depth
  for x in node.traverse(t.list) do
    local id = x.id
    if id == GLUE then
      y = y + node.effective_glue(x, t)
      if y > maxb then maxb = y end
    elseif id == KERN then
      y = y + x.kern
      if y > maxb then maxb = y end
    elseif id == HLIST or id == VLIST then
      y = y + x.height
      if y + x.depth > maxb then maxb = y + x.depth end
      y = y + x.depth
    end
  end
  return maxb - t.height
end

-- 垂直リストの最後の要素が，その基準線より下に見かけの上で出る分
-- （行なら深さ．垂直の箱なら，中身が箱の下端からはみ出す分も含める．中身を
-- グルーで下へずらして負のグルーで戻す箱もあるので，グルーで下った位置も見る）
local function overhang(head)
  if not head then return 0 end
  local t = node.tail(head)
  while t and t.id == WHATSIT do t = t.prev end
  if not t then return 0 end
  if t.id == HLIST then return t.depth end
  if t.id == VLIST then return vbox_over(t) end
  return 0
end

-- 垂直リストの最後の箱のベースラインの位置（上端から．グルーは自然長）
local function lastbase(head)
  if not head then return 0 end
  local y, base = 0, 0
  for n in node.traverse(head) do
    local id = n.id
    if id == GLUE then y = y + n.width
    elseif id == KERN then y = y + n.kern
    elseif id == HLIST or id == VLIST or id == nodeid('rule') then
      y = y + n.height
      base = y
      y = y + n.depth
    end
  end
  return base
end

local function boxlist_copy(n)
  local b = n and tex.getbox(n)
  if b and b.list then return copy_list(b.list) end
  return nil
end

-- 中身も寸法もない箱（段数の切り換えで置く空の箱）
local function is_emptybox(n)
  if not ((n.id == HLIST or n.id == VLIST) and n.height == 0 and n.depth == 0
          and n.width == 0) then
    return false
  end
  -- 中身があっても，whatsit（LuaTeX-jaなどが入れる）や幅のない要素だけなら空とみなす
  for m in node.traverse(n.list) do
    local id = m.id
    if not (id == WHATSIT or id == PENALTY or (id == GLUE and m.width == 0)
            or (id == KERN and m.kern == 0)) then
      return false
    end
  end
  return true
end

-- 末尾の除去可能な項目（グルー・カーン・ペナルティ）を取り除く．allなら
-- 空の箱も取り除く
local function strip_tail(head, all)
  if not head then return nil end
  if all then
    -- whatsit（脚注の参照位置の印など）は残して，その前後の除去可能な項目と
    -- 空の箱を取り除く
    local t = node.tail(head)
    while t and (t.id == WHATSIT or is_discardable(t) or is_emptybox(t)) do
      local p = t.prev
      if t.id ~= WHATSIT then
        head = node.remove(head, t)
        node.free(t)
      end
      t = p
    end
    return head
  end
  local t = node.tail(head)
  while t and is_discardable(t) do
    if not (t.id == GLUE and t.stretch_order > 0)
       and not (t.id == PENALTY and t.penalty <= -10000) then
      break
    end
    local p = t.prev
    head = node.remove(head, t)
    node.free(t)
    t = p
  end
  return head
end

-- 先頭側で最初に現れる\topskipグルーを取り除く（箱より前にあるものだけ）
local function strip_topskip(head)
  local n = head
  while n do
    local id = n.id
    if id == HLIST or id == VLIST or id == nodeid('rule') then break end
    if id == GLUE and n.subtype == TOPSKIP then
      head = node.remove(head, n)
      node.free(n)
      break
    end
    n = n.next
  end
  return head
end

------------------------------------------------------------------------
-- 脚注の参照位置
------------------------------------------------------------------------

function M.setattr(a) M.fnattr = a end

function M.newfn()
  M.fncount = M.fncount + 1
  M.curfn = M.fncount
  tex.setattribute(M.fnattr, M.curfn)
end

function M.anchor()
  local w = node.new(WHATSIT, USERDEF)
  w.user_id = USER_ID
  w.type = 100
  w.value = M.curfn
  node.write(w)
end

local function collect_ids(head, out)
  for n in node.traverse(head) do
    local id = n.id
    if id == WHATSIT and n.subtype == USERDEF and n.user_id == USER_ID then
      out[#out + 1] = n.value
    elseif (id == HLIST or id == VLIST) and n.list then
      collect_ids(n.list, out)
    end
  end
  return out
end

------------------------------------------------------------------------
-- 段の取り込み
------------------------------------------------------------------------

function M.capture(footins)
  local c = { top = {}, bot = {} }
  c.text = boxlist_copy(255)
  -- 改段位置から後ろの除去可能項目は，次の段の先頭で捨てられてしまうので
  -- ここで写しをとっておく．改段位置のペナルティはTeXが10000に書き換えている
  -- ので，元の値（\outputpenalty）に戻す（強制改段は強制改段のまま残し，
  -- 揃えるときにもそこで段を改める）
  local d = newlist()
  local n = tex.lists.contrib_head
  local op = tex.outputpenalty
  local first = true
  while n and is_discardable(n) do
    local x = node.copy(n)
    if first and x.id == PENALTY then
      x.penalty = (op <= -10000) and -10000 or op
    end
    first = false
    append(d, x)
    n = n.next
  end
  c.disc = d.head
  c.forced = op <= -10000  -- この段は強制改段で終わった
  c.fn = boxlist_copy(footins)
  M.cols[#M.cols + 1] = c
  info('captured column %d', #M.cols)
end

-- \@makecolが組んだ段の箱のはみ出しを記録する（そのページを組み直さずに出力する
-- ときだけ警告を出す．組み直すなら捨てる箱なので警告しない）
function M.checkcol(boxnum, fuzz)
  local c = M.cols[#M.cols]
  local b = tex.getbox(boxnum)
  if not (c and b and b.list) then return end
  -- TeXと同じく，縮められるグルーを縮めても入らないときだけはみ出しとみなす
  local nat = vpack(copy_list(b.list))
  local over = nat.height - b.height
  node.free(nat)
  local fit, bad = vpack(copy_list(b.list), b.height, 'exactly')
  node.free(fit)
  if bad and bad >= 1000000 and over > fuzz then c.overfull = over end
end

function M.reportoverfull()
  for _, c in ipairs(M.cols) do
    if c.overfull then
      info('overfull column built by LaTeX (\\@makecol), shipped as is')
      texio.write_nl(string.format(
        'Overfull \\vbox (%s too high) has occurred while \\output is active []', pt(c.overfull)))
      texio.write_nl('')
    end
  end
end

-- 行の箱nの中の字の高さと深さの最大（字がなければnil）．段間罫を行の字（和字では
-- 字の枠）の上端・下端で止めるのに使う（行の箱の寸法には支柱の分が入ることがある）
-- 字の輪郭（曲線）から求めた正確な字面の上端・下端（ベースラインからの高さと深さ）．
-- フォントの字の高さと深さは輪郭の制御点まで含めた外接矩形なので，曲線の多い字
-- （「無」の点など）では字面より大きい．段間罫の端を決める行だけに使う
local shapes, tightcache = {}, {}
local function tight_glyph(g)
  local f = font.getfont(g.font)
  local key = g.font .. ':' .. g.char
  local c = tightcache[key]
  if c ~= nil then return c ~= false and c[1] or nil, c ~= false and c[2] or nil end
  local res = false
  local ch = f and f.characters and f.characters[g.char]
  local file = f and f.filename
  if ch and ch.index and file and fonts and fonts.handlers and fonts.handlers.otf
    and fonts.handlers.otf.readers and fonts.handlers.otf.readers.loadshapes then
    local sh = shapes[file]
    if sh == nil then
      local ok, r = pcall(fonts.handlers.otf.readers.loadshapes, file)
      sh = ok and r or false
      shapes[file] = sh
    end
    local gl = sh and sh.glyphs and sh.glyphs[ch.index]
    if gl and gl.segments and (sh.units or 0) > 0 then
      local ymin, ymax
      local function add(y)
        if not ymin or y < ymin then ymin = y end
        if not ymax or y > ymax then ymax = y end
      end
      local function cubic(y0, y1, y2, y3)
        add(y3)
        -- 導関数の根（0<t<1）での値
        local a = -y0 + 3 * y1 - 3 * y2 + y3
        local b = 2 * (y0 - 2 * y1 + y2)
        local cc = y1 - y0
        local function at(t)
          if t > 0 and t < 1 then
            local u = 1 - t
            add(u * u * u * y0 + 3 * u * u * t * y1 + 3 * u * t * t * y2 + t * t * t * y3)
          end
        end
        if math.abs(a) < 1e-9 then
          if math.abs(b) > 1e-9 then at(-cc / b) end
        else
          local disc = b * b - 4 * a * cc
          if disc >= 0 then
            local r = math.sqrt(disc)
            at((-b + r) / (2 * a)); at((-b - r) / (2 * a))
          end
        end
      end
      local cy = 0
      for _, sg in ipairs(gl.segments) do
        local op = sg[#sg]
        if op == 'm' or op == 'l' then cy = sg[2]; add(cy)
        elseif op == 'c' then cubic(cy, sg[2], sg[4], sg[6]); cy = sg[6]
        elseif op == 'q' then  -- 2次曲線は3次に直す
          local y1, y2 = sg[2], sg[4]
          cubic(cy, cy + 2 / 3 * (y1 - cy), y2 + 2 / 3 * (y1 - y2), y2); cy = y2
        end
      end
      if ymin then
        local sc = f.size / sh.units
        res = { math.floor(ymax * sc + 0.5), math.floor(-ymin * sc + 0.5) }
      end
    end
  end
  tightcache[key] = res
  if res then return res[1], res[2] end
  return nil
end
-- 行（hlist）の字面の上端・下端（ベースラインからの高さと深さ）．tightなら輪郭から求める
local function line_extent(n, tight)
  local mh, md
  for g in node.traverse(n.list) do
    if g.id == GLYPH then
      local gh, gd = g.height, g.depth
      if tight and gh + gd > 0 then
        local th, td = tight_glyph(g)
        if th then gh, gd = math.min(gh, th), math.min(gd, td) end
      end
      if not mh or gh > mh then mh = gh end
      if not md or gd > md then md = gd end
    elseif g.id == HLIST and g.list then
      local a, b = line_extent(g, tight)
      if a then
        a, b = a - g.shift, b + g.shift
        if not mh or a > mh then mh = a end
        if not md or b > md then md = b end
      end
    end
  end
  return mh, md
end
-- 段間罫の端：要素r（{q=箱, y=箱の上端の位置}）の字面の上端と下端．行は行の中の字の
-- 輪郭で見る．字のない箱と罫は箱の大きさで見る
local function edge_top(r)
  if not r then return nil end
  local q = r.q
  if q.id == HLIST and q.list then
    local h = line_extent(q, true)
    if h then return r.y + q.height - h end
  end
  return r.y
end
local function edge_bot(r)
  if not r then return nil end
  local q = r.q
  if q.id == HLIST and q.list then
    local _, d = line_extent(q, true)
    if d then return r.y + q.height + d end
  end
  return r.y + q.height + q.depth
end
-- LaTeXが組む段の段間罫：組み上げた段の箱（\@outputbox）をたどり，上のnt個と下のnb個の
-- フロート（場所取りを含む）を除いて，下のフロートより前（本文と，その下の脚注）と後
-- （spanfootnote=bottomの脚注）の，最初の要素の上端と最後の要素の下端を求める．
-- 行は行の中の字の上端・下端で見る．フロートに接する罫（\topfigruleなど）は除く．
-- 段colnoの右の段の場所取りの有無（phtop，phbot）で，左の段との間の罫の区間を決める
local texprev
function M.colrule(boxnum, colno, nt, nb, phtop, phbot)
  local b = tex.getbox(boxnum)
  local items = {}
  if b and b.list then
    local y = 0
    for q in node.traverse(b.list) do
      local id = q.id
      if id == GLUE then y = y + node.effective_glue(q, b)
      elseif id == KERN then y = y + q.kern
      elseif id == HLIST or id == VLIST or id == RULE then
        if q.height + q.depth > 0 then
          items[#items + 1] = { v = id == VLIST, r = id == RULE, q = q, y = y }
        end
        y = y + q.height + q.depth
      end
    end
  end
  -- 上のnt個と下のnb個のVLISTがフロート
  local nv = 0
  for _, it in ipairs(items) do if it.v then nv = nv + 1 end end
  local k = 0
  for _, it in ipairs(items) do
    if it.v then
      k = k + 1
      if k <= nt then it.ft = true elseif k > nv - nb then it.fb = true end
    end
  end
  for j, it in ipairs(items) do
    if it.r and ((items[j - 1] and items[j - 1].ft) or (items[j + 1] and items[j + 1].fb)) then it.skip = true end
  end
  local g, seenbot = {}, false
  for _, it in ipairs(items) do
    if it.fb then seenbot = true
    elseif not (it.ft or it.skip) then
      if not seenbot then g.top = g.top or it; g.bot = it
      else g.fntop = g.fntop or it; g.fnbot = it end
    end
  end
  local function lo(x, y2) if x and y2 then return math.min(x, y2) end return x or y2 end
  local function hi(x, y2) if x and y2 then return math.max(x, y2) end return x or y2 end
  local rtop, rend, r2top, r2end = 0, 0, 0, 0
  local a = colno > 1 and texprev or nil
  if a and phtop then rtop = lo(edge_top(a.top), edge_top(g.top)) or 0 end
  if a and phbot then
    rend = hi(edge_bot(a.bot), edge_bot(g.bot)) or 0
    r2top = lo(edge_top(a.fntop), edge_top(g.fntop)) or 0
    r2end = hi(edge_bot(a.fnbot), edge_bot(g.fnbot)) or 0
  end
  texprev = g
  tex.setdimen('global', 'evenend@rtop', rtop)
  tex.setdimen('global', 'evenend@rend', rend)
  tex.setdimen('global', 'evenend@rtwotop', r2top)
  tex.setdimen('global', 'evenend@rtwoend', r2end)
end

-- 段をまたぐフロートの箱（段数k）と場所取りの箱に印を付ける
function M.markspan(boxnum, k)
  local b = tex.getbox(boxnum)
  if b then node.set_attribute(b, SPAN, k) end
end
-- 幅wの段をまたぐフロートが，段幅cw・段間sepの段組でまたがる段数（tex.sprintで返す）
function M.spank(w, cw, sep)
  local k = math.ceil((w + sep) / (cw + sep) - 0.001)
  if k < 1 then k = 1 end
  tex.sprint(tostring(k))
end
function M.markph(boxnum)
  local b = tex.getbox(boxnum)
  if b then node.set_attribute(b, PH, 1) end
end

-- span：段をまたぐフロートなら段数，場所取りなら-1（TeX側の記録から）
local function markcopy(b, span)
  local n = node.copy(b)
  if span and span > 0 then node.set_attribute(n, SPAN, span)
  elseif span and span < 0 then node.set_attribute(n, PH, 1) end
  return n
end
function M.addfloat(where, boxnum, span)
  local c = M.cols[#M.cols]
  local b = tex.getbox(boxnum)
  if c and b then
    table.insert(c[where], markcopy(b, span))
  end
end

-- まだ出ていない（持ち越された）フロート：kindは'col'（段内）か'dbl'（段抜き）
M.deferred = { col = {}, dbl = {} }
function M.adddeferred(kind, boxnum, span, fps)
  local b = tex.getbox(boxnum)
  if b then
    local n = markcopy(b, span)
    if fps then node.set_attribute(n, FPS, fps) end
    table.insert(M.deferred[kind], n)
  end
end

-- フロートだけの段（LaTeXが\@tryfcolumnで作る）：その中身を自然な高さに組み直して
-- 上のフロートとして取り込む
function M.capturefcol(boxnum)
  local b = tex.getbox(boxnum)
  local c = { top = {}, bot = {}, fcol = true }
  if b and b.list then
    local l = copy_list(b.list)
    -- 上下の伸びるグルー（\@fptop，\@fpbot）は自然長にする
    c.top[1] = vpack(l)
  end
  M.cols[#M.cols + 1] = c
  info('captured float column %d', #M.cols)
end

-- 本文のない段（持ち越されたフロートだけでブロックを組むとき）
function M.emptycolumn()
  M.cols[#M.cols + 1] = { top = {}, bot = {} }
end

local function free_col(c)
  if c.text then flush_list(c.text) end
  if c.disc then flush_list(c.disc) end
  if c.fn   then flush_list(c.fn) end
  for _, f in ipairs(c.top) do node.free(f) end
  for _, f in ipairs(c.bot) do node.free(f) end
end

function M.reset()
  for _, c in ipairs(M.cols) do free_col(c) end
  M.cols = {}
  for _, k in ipairs({ 'col', 'dbl' }) do
    for _, f in ipairs(M.deferred[k]) do node.free(f) end
    M.deferred[k] = {}
  end
  if M.pool then
    for _, f in ipairs(M.pool) do if f.box then node.free(f.box) end end
    M.pool = nil
  end
  if M.dblbox then node.free(M.dblbox); M.dblbox = nil end
  if M.out then
    for _, b in pairs(M.out) do node.free(b) end
    M.out = nil
  end
end

------------------------------------------------------------------------
-- 本文中のフロート（[h]）の行ドリ
------------------------------------------------------------------------

-- 本文の行（中身のある水平の箱）か
local function is_line(n)
  return n.id == HLIST and n.list ~= nil and has_attr(n, INTEXT) ~= 1
end

-- 垂直リストでの要素の縦の長さ（グルーは自然長）
local function vsize(n)
  local id = n.id
  if id == GLUE then return n.width end
  if id == KERN then return n.kern end
  if id == HLIST or id == VLIST or id == nodeid('rule') then
    return n.height + n.depth
  end
  return 0
end

-- 本文中のフロート（前後に\intextsepのグルーがある垂直の箱）に印を付ける．
-- 行送りの位置への調整は，段に分けた後でsnap_chunkが行う
local function mark_intext(head, bs)
  local its = tex.getglue('intextsep')
  local function near(n, dir)
    n = n and n[dir]
    while n and n.id == PENALTY do n = n[dir] end
    return n
  end
  local function is_its(g) return g and g.id == GLUE and math.abs(g.width - its) < 2 end
  local n = head
  while n do
    if n.id == VLIST then
      local g1, g2 = near(n, 'prev'), near(n, 'next')
      -- 印は片側だけでも付ける（ページの先頭では前のグルーが捨てられている）
      if is_its(g1) or is_its(g2) then node.set_attribute(n, INTEXT, 1) end
    end
    -- 本文中の高い箱（tcolorboxなど．1.5行を超えるもの）も，本文中のフロートと
    -- 同じく分けられない塊として扱う
    if (n.id == HLIST or n.id == VLIST) and bs and bs > 0
       and n.height + n.depth > 1.5 * bs and has_attr(n, INTEXT) ~= 1 then
      node.set_attribute(n, INTEXT, 1)
    end
    n = n.next
  end
end

-- 本文中のフロートか（mark_intextが印を付けた垂直の箱）
local function is_intext(n)
  return n and (n.id == VLIST or n.id == HLIST) and has_attr(n, INTEXT) == 1
end

-- 段に分けた後の本文（段の上端から始まる）で，本文中のフロートの直後の行が段の
-- 行の位置（\topskip＋行送りの倍数）に乗るように，フロートの前後のグルーを
-- 広げる（前後に半分ずつ．段の先頭のフロートは後ろだけ）
local function snap_chunk(head, topskip, bs)
  if not head or bs <= 0 then return end
  local y, n = 0, head
  while n do
    local id = n.id
    if id == GLUE then y = y + n.width
    elseif id == KERN then y = y + n.kern
    elseif id == HLIST or id == VLIST or id == nodeid('rule') then
      if is_intext(n) then
        -- 直後の行と，その行までのグルー
        local ya, q, gafter = y + n.height + n.depth, n.next, nil
        while q and not is_line(q) do
          if not gafter and q.id == GLUE then gafter = q end
          ya = ya + vsize(q); q = q.next
        end
        -- フロートの前後のグルーは伸縮させない（段を詰めるときに伸縮すると，後の
        -- 行が行送りの位置からずれる）
        -- （前後の行とのあいだのグルーはすべて）
        local function rigid(g) if g then node.setglue(g, g.width, 0, 0, 0, 0) end end
        do
          local m = n.next
          while m and m ~= q do
            if m.id == GLUE then rigid(m) end
            m = m.next
          end
          m = n.prev
          while m and not is_line(m) and m.id ~= VLIST do
            if m.id == GLUE then rigid(m) end
            m = m.prev
          end
        end
        if q and gafter then
          local base = ya + q.height
          local r = (base - topskip) % bs
          if r > 655 and bs - r > 655 then
            local delta = bs - r
            -- 前のグルー（直前の行とのあいだ）
            local gbefore, m = nil, n.prev
            while m and not is_line(m) and m.id ~= VLIST do
              if m.id == GLUE then gbefore = m; break end
              m = m.prev
            end
            if gbefore then
              local half = math.floor(delta / 2)
              gbefore.width = gbefore.width + half
              gafter.width = gafter.width + (delta - half)
              y = y + half
            else
              gafter.width = gafter.width + delta
            end
          end
        end
      end
      y = y + n.height + n.depth
    end
    n = n.next
  end
end

-- 段の末尾が本文中のフロートか
local function ends_intext(head)
  if not head then return false end
  local t = node.tail(head)
  while t and (is_discardable(t) or t.id == WHATSIT) do t = t.prev end
  return t and is_intext(t)
end

------------------------------------------------------------------------
-- 均し
------------------------------------------------------------------------

-- p: TeX側から渡される設定
--   N：段数
--   colht：段の高さ（\@colht）
--   colmode：脚注を段の下端に置くか（falseなら版面下端）
--   footins：脚注の挿入番号
--   blskip：\baselineskip（段を下揃えにするかの判定用）
--   scratch：作業用のボックスレジスタ
--   topfig, botfig, fnrule：\topfigrule, \botfigrule, \footnoteruleを組んだボックス
--   block：段数を切り換える前の段組（ブロック）として揃える．脚注は段の下端に
--     置き，段の箱の高さは揃えた高さにする
-- 次のページへ送り返す本文restに，その中で参照する脚注を\insertにして付ける
-- （参照位置の印の直後．印が箱の中にあればその箱の直後）．送り返すものがなければnil
local INS = nodeid('ins')
local function make_push(rest, segs, p)
  local keep = false
  for n in node.traverse(rest) do
    local id = n.id
    if id ~= GLUE and id ~= KERN and id ~= PENALTY then keep = true break end
  end
  if not keep then flush_list(rest) return nil end
  local function mkins(id)
    local s = segs[id]
    if not (s and s.head) then return nil end
    local ins = node.new(INS)
    ins.subtype = p.footins
    local h, d = natural(s.head)
    ins.head = s.head
    s.head = nil
    ins.height = h + d
    ins.depth = p.fnsmd or 0
    ins.cost = p.fnfloatpen or 20000
    ins.width = p.fnsep or 0  -- \splittopskip（\footnotesep）
    return ins
  end
  local n = rest
  while n do
    local nx = n.next
    local ids
    if n.id == WHATSIT and n.subtype == USERDEF and n.user_id == USER_ID then
      ids = { n.value }
    elseif (n.id == HLIST or n.id == VLIST) and n.list then
      ids = collect_ids(n.list, {})
    end
    if ids then
      local at = n
      for _, id in ipairs(ids) do
        local ins = mkins(id)
        if ins then
          rest = node.insert_after(rest, at, ins)
          at = ins
        end
      end
    end
    n = nx
  end
  return rest
end
function M.getfn(n)
  tex.setbox(n, M.fnlist and vpack(M.fnlist) or nil)
  M.fnlist = nil
end
-- 送り返した本文の後に続く材料の先頭：改ページ位置のペナルティはTeXが10000に
-- 書き換えているので，元の値に戻す（送り返した本文の後でまた改ページできるように）
function M.fixcontrib()
  local n = tex.lists.contrib_head
  local op = tex.outputpenalty
  if n and n.id == PENALTY and n.penalty == 10000 and op ~= 10000 then n.penalty = op end
end
function M.getpush(n)
  tex.setbox(n, M.push and vpack(M.push) or nil)
  M.push = nil
end

function M.balance(p)
  local cols = M.cols
  local N, colht = p.N, p.colht
  -- footnote=page：脚注は段に入れず，版面の全幅で版面の下端に置く（multicolと同じ）．
  -- 段の高さは，ページの脚注の分を除いた高さになる
  local fullfn = p.fullfn and not p.colmode
  if fullfn then p.spanfnbottom = false end
  if p.block and not fullfn then p.colmode = true end
  -- spanfootnote=bottom：揃える段組では，脚注の下端を段の下端に置く（段下端の脚注）
  if p.spanfnbottom then p.colmode = true end
  -- 行送りへの切り上げで入り切らなければ，切り上げずにやり直すので，持ち越された
  -- フロートの写しをとっておく
  local saved_deferred
  if (p.relaxed or 0) < 2 then
    saved_deferred = { col = {}, dbl = {} }
    for _, k in ipairs({ 'col', 'dbl' }) do
      for _, f in ipairs(M.deferred[k]) do table.insert(saved_deferred[k], node.copy(f)) end
    end
  end
  local function drop_saved()
    if saved_deferred then
      for _, k in ipairs({ 'col', 'dbl' }) do
        for _, f in ipairs(saved_deferred[k]) do node.free(f) end
      end
      saved_deferred = nil
    end
  end
  -- 持ち越された段抜きフロートは，揃えた段組の下に段抜きで置く
  local dblfloats = M.deferred.dbl
  M.deferred.dbl = {}
  local dblh = 0
  if #dblfloats > 0 then
    dblh = tex.getglue('dbltextfloatsep')
    for j, f in ipairs(dblfloats) do
      dblh = dblh + f.height + f.depth + (j > 1 and tex.getglue('dblfloatsep') or 0)
    end
    colht = colht - dblh
  end
  local function drop_dbl()
    for _, f in ipairs(dblfloats) do node.free(f) end
    dblfloats = {}
  end
  tex.setcount('global', 'evenend@status', 0)
  tex.setdimen('global', 'evenend@headshift', 0)
  if #cols == 0 then
    info('nothing captured')
    drop_dbl(); drop_saved()
    return
  end
  if #cols > N then
    info('captured %d columns for %d', #cols, N)
    drop_dbl(); drop_saved()
    return
  end

  -- 1. 本文を1本の垂直リストに繋ぎ直す（取り込んだ材料は複製して使い，
  -- 失敗したときにやり直せるように残しておく）
  local text = newlist()
  for k, c in ipairs(cols) do
    local t = c.text and copy_list(c.text)
    -- 強制改段で終わった段（最後の段を除く）は，改段の前の\vfilを残す
    if k == #cols or not c.forced then t = strip_tail(t, k == #cols) end
    if k > 1 then
      t = strip_topskip(t)
      append(text, cols[k - 1].disc and copy_list(cols[k - 1].disc))
    end
    append(text, t)
  end
  text.head = strip_tail(text.head, true)
  if not text.head then text.head = mkglue(0) end  -- 本文がない
  -- 本文中のフロートに印を付ける
  mark_intext(text.head, p.blskip)
  if os.getenv('EVENEND_TRACE') then  -- 調査用：本文の要素
    local out = {}
    for n in node.traverse(text.head) do
      local id = n.id
      if id == GLUE then out[#out + 1] = string.format('g%.1f', n.width / 65536)
      elseif id == KERN then out[#out + 1] = string.format('k%.1f', n.kern / 65536)
      elseif id == PENALTY then out[#out + 1] = 'p' .. n.penalty
      elseif id == HLIST or id == VLIST then
        out[#out + 1] = string.format('%s(%.1f+%.1f)', id == HLIST and 'H' or 'V', n.height / 65536, n.depth / 65536)
      else out[#out + 1] = node.type(id):sub(1, 2) end
    end
    info('    text: %s', table.concat(out, ' '))
  end

  -- 2. 脚注を番号ごとの断片に分ける（段をまたいで分割されたものは繋ぐ）
  local fnattr = M.fnattr
  local segs, segorder = {}, {}
  for k, c in ipairs(cols) do
    local pending = newlist()
    local last
    local n = c.fn and copy_list(c.fn)
    while n do
      local nx = n.next
      n.next, n.prev = nil, nil
      local id = has_attr(n, fnattr)
      if id then
        local s = segs[id]
        if not s then
          s = newlist()
          s.col = k
          segs[id] = s
          segorder[#segorder + 1] = id
        end
        append(s, pending.head)
        pending = newlist()
        append(s, n)
        last = s
      else
        append(pending, n)
      end
      n = nx
    end
    if pending.head then
      if last then
        append(last, pending.head)
      else
        -- どの脚注にも属さない材料：その段に固定する
        local id = -k
        local s = newlist()
        s.col = k
        append(s, pending.head)
        segs[id] = s
        segorder[#segorder + 1] = id
      end
    end
  end
  for _, id in ipairs(segorder) do
    local s = segs[id]
    s.ht, s.dp = natural(s.head)
  end

  -- 本文中に参照位置のない脚注は元の段に固定する
  local anchored = {}
  for _, id in ipairs(collect_ids(text.head, {})) do anchored[id] = true end
  local orphans = {}
  for i = 1, N do orphans[i] = {} end
  for _, id in ipairs(segorder) do
    if not anchored[id] then
      local k = segs[id].col
      table.insert(orphans[k], id)
    end
  end

  local fs   = { tex.getglue(p.footins) }
  local footskip = fs[1]
  local rule_h
  do
    local rb = tex.getbox(p.fnrule)
    rule_h = rb and (rb.height + rb.depth) or 0
  end

  local function fnblock(ids)
    local n, sum, lastd = 0, 0, 0
    for _, id in ipairs(ids) do
      local s = segs[id]
      if s then
        n = n + 1
        sum = sum + s.ht + s.dp
        lastd = s.dp
      end
    end
    if n == 0 then return 0, 0 end
    return footskip + rule_h + sum - lastd, lastd
  end

  local function fnids(i, ids)
    if fullfn then return {} end
    local r = {}
    for _, id in ipairs(orphans[i]) do r[#r + 1] = id end
    for _, id in ipairs(ids) do
      if segs[id] and anchored[id] then r[#r + 1] = id end
    end
    return r
  end

  -- footnote=page：ページの脚注（全幅）に加える脚注idsの分，段の高さが減る．
  -- このページの前のブロックの脚注があれば（p.fnold：その脚注の領域の高さ，
  -- p.fnoldd：その最後の行の深さ），その下に続ける
  local fnskip0 = p.fnskip or footskip
  local function fullspace(ids)
    local n, sum, lastd = 0, 0, 0
    for _, id in ipairs(ids) do
      local s = segs[id]
      if s then n = n + 1; sum = sum + s.ht + s.dp; lastd = s.dp end
    end
    if n == 0 then return 0 end
    if (p.fnold or 0) > 0 then return sum + (p.fnoldd or 0) - lastd end
    return fnskip0 + rule_h + sum - lastd
  end
  -- ページの脚注：本文中に参照位置のないもの（前のページから続く脚注など）を先に，
  -- 次に本文での参照の順
  local orphan_all = {}
  for _, id in ipairs(segorder) do
    if not anchored[id] then orphan_all[#orphan_all + 1] = id end
  end
  local function pageids(lists)
    local r, seen = {}, {}
    for _, id in ipairs(orphan_all) do r[#r + 1] = id; seen[id] = true end
    for _, ids in ipairs(lists) do
      for _, id in ipairs(ids) do
        if segs[id] and anchored[id] and not seen[id] then r[#r + 1] = id; seen[id] = true end
      end
    end
    return r
  end
  local curFT = 0
  if fullfn then curFT = fullspace(pageids({ collect_ids(text.head, {}) })) end

  -- headingskip=block：前のブロックに続く2段以上のブロックが見出しで始まるとき，
  -- ブロック全体を見出しの上アキ（見出しの字面の上端が通常の1行目の上端より
  -- 下がっている分．行送りの倍数に丸める）だけ下げる．ブロックの中の組は変えない．
  -- ブロックの間のアキが，1段のブロック（見出しの上アキがブロックの間に見える）と
  -- 同じになる
  local headshift = 0
  if p.headblock and N > 1 then
    local function has_glyph(b)
      for c in node.traverse(b.list) do
        if c.id == GLYPH then return true end
        if (c.id == HLIST or c.id == VLIST) and c.list and has_glyph(c) then return true end
      end
      return false
    end
    -- 箱bの中で字を含む最初の行の上端（bの上端をy0として）
    local function inktop(b, y0)
      local y = y0
      for c in node.traverse(b.list) do
        if c.id == GLUE then y = y + c.width
        elseif c.id == KERN then y = y + c.kern
        elseif c.id == HLIST then
          if c.list and has_glyph(c) then return y end
          y = y + c.height + c.depth
        elseif c.id == VLIST then
          local r = c.list and inktop(c, y)
          if r then return r end
          y = y + c.height + c.depth
        elseif c.id == RULE then y = y + c.height + c.depth
        end
      end
      return nil
    end
    -- 本文の行の標準の高さ
    local lineht, cnt, best = 0, {}, 0
    for n in node.traverse_id(HLIST, text.head) do
      if n.list then
        cnt[n.height] = (cnt[n.height] or 0) + 1
        if cnt[n.height] > best then best, lineht = cnt[n.height], n.height end
      end
    end
    -- 先頭の箱（見出しを行取りした垂直の箱）を探す
    local y, n = 0, text.head
    while n and n.id ~= HLIST and n.id ~= VLIST and n.id ~= RULE do
      if n.id == GLUE then y = y + n.width elseif n.id == KERN then y = y + n.kern end
      n = n.next
    end
    local top = n and n.id == VLIST and n.list and inktop(n, y)
    if top then
      local u = top - (tex.getglue('topskip') - lineht)
      if p.blskip > 0 then u = math.floor(u / p.blskip + 0.5) * p.blskip end
      if u > 0 then
        headshift = u
        colht = colht - u
        info('block lowered by the heading space %s', pt(u))
      end
    end
  end

  -- 3. 段ごとのフロートの占める高さ
  local floatsep     = tex.getglue('floatsep')
  local textfloatsep = tex.getglue('textfloatsep')
  local function boxh(n)
    local b = tex.getbox(n)
    return b and (b.height + b.depth) or 0
  end
  local topfig_h, botfig_h = boxh(p.topfig), boxh(p.botfig)
  -- フロートまわりのグルーの縮み（有限のものだけ）
  local function shrink(name)
    local _, _, sh, _, sho = tex.getglue(name)
    return sho == 0 and sh or 0
  end
  local fs_sh, tfs_sh = shrink('floatsep'), shrink('textfloatsep')
  -- ブロックのフロート（段に置かれたものと持ち越されたもの）を番号順に並べる
  -- 段をまたぐフロートは段数spanを持つ．場所取りの箱は捨て，割り振りに合わせて作り直す
  local F = {}
  local function spanof(b)
    local k = node.has_attribute(b, SPAN)
    if k and k > 1 and k <= N then return k end
    return nil
  end
  for k, c in ipairs(cols) do
    for _, pos in ipairs({ 'top', 'bot' }) do
      for _, f in ipairs(c[pos]) do
        if not node.has_attribute(f, PH) then
          F[#F + 1] = { box = node.copy(f), pos = pos, orig = k, span = spanof(f) }
        end
      end
    end
  end
  for _, f in ipairs(M.deferred.col) do
    -- 段をまたぐフロートは，位置の指定（\countのビット：2が上，4が下）に下が
    -- あれば下にも置ける
    local fps = node.has_attribute(f, FPS) or 2
    F[#F + 1] = { box = f, pos = 'top', orig = 1, deferred = true, span = spanof(f),
                  canbot = p.deferbot ~= false and (fps // 4) % 2 == 1,
                  cantop = (fps // 2) % 2 == 1 }
  end
  M.deferred.col = {}
  M.pool = F  -- 失敗したときにM.resetが片付ける

  -- 段ごとのフロートの並び（割り振りassignから作る）と占める高さ
  local tops, bots = {}, {}
  local fl_top, fl_bot, fl_shrink = {}, {}, {}
  -- floatgrid：フロートの並び（アキを含む）の高さを行送りの倍数に切り上げ，
  -- 後に続く本文の行が行送りの位置からずれないようにする．足した分
  local ext_top, ext_bot = {}, {}
  local function snap(x)
    if not p.floatgrid or x == 0 or p.blskip <= 0 then return x, 0 end
    local r = x % p.blskip
    if r < 655 or p.blskip - r < 655 then return x, 0 end  -- 0.01pt
    return x + p.blskip - r, p.blskip - r
  end
  local function set_assign(assign)
    for i = 1, N do tops[i], bots[i] = {}, {} end
    -- 段をまたぐフロートとその場所取りは，上なら段の最初，下なら段の最後に置く
    -- （またがる段のあいだで位置がそろうように）
    local spantop, spanbot = {}, {}
    for j, f in ipairs(F) do
      local c = math.abs(assign[j])
      if f.span then
        if f.deferred then f.pos = assign[j] < 0 and 'bot' or 'top' end
        local lst = f.pos == 'top' and spantop or spanbot
        lst[c] = lst[c] or {}
        table.insert(lst[c], f.box)
        f.ph = f.ph or {}
        for m = 1, f.span - 1 do
          if not f.ph[m] then
            local v = node.new(VLIST)
            v.width, v.height, v.depth = 0, f.box.height, f.box.depth
            node.set_attribute(v, PH, 1)
            f.ph[m] = v
          end
          lst[c + m] = lst[c + m] or {}
          table.insert(lst[c + m], f.ph[m])
        end
      else
        table.insert(f.pos == 'top' and tops[c] or bots[c], f.box)
      end
    end
    for i = 1, N do
      if spantop[i] then
        for k = #spantop[i], 1, -1 do table.insert(tops[i], 1, spantop[i][k]) end
      end
      if spanbot[i] then
        for _, b in ipairs(spanbot[i]) do table.insert(bots[i], b) end
      end
    end
    for i = 1, N do
      local t, b = 0, 0
      for j, f in ipairs(tops[i]) do
        t = t + f.height + f.depth + (j > 1 and floatsep or 0)
      end
      if #tops[i] > 0 then t = t + topfig_h + textfloatsep end
      for j, f in ipairs(bots[i]) do
        b = b + f.height + f.depth + (j > 1 and floatsep or 0)
      end
      if #bots[i] > 0 then b = b + botfig_h + textfloatsep end
      fl_top[i], ext_top[i] = snap(t)
      fl_bot[i], ext_bot[i] = snap(b)
      local n = #tops[i] + #bots[i]
      fl_shrink[i] = 0
      if p.floatgrid then
        -- 上のフロートまわりのアキは伸縮させない（本文が行の位置からずれるので）
        if #bots[i] > 0 then fl_shrink[i] = tfs_sh + (#bots[i] - 1) * fs_sh end
      elseif n > 0 then
        fl_shrink[i] = (#tops[i] > 0 and tfs_sh or 0) + (#bots[i] > 0 and tfs_sh or 0)
                       + (n - (#tops[i] > 0 and 1 or 0) - (#bots[i] > 0 and 1 or 0)) * fs_sh
      end
    end
  end

  -- 段iの下に段をまたぐフロートか場所取りがあるか．その段では，footnote=pageでも
  -- 脚注を版面の下端でなくフロートの上に置く（段の下端モードと同じに扱う．LaTeXが組む
  -- 段の\evenend@fnabovespanと同じ）．またがる段のあいだでフロートの位置がそろう
  -- spanfootnote=bottom：揃える段組（最終ページとブロック）では，すべての段で脚注の
  -- 下端を段の下端に置き（段下端の脚注と同じ組み方），段をまたぐ図は，またがる段の
  -- うちいちばん高い脚注の上にそろえる
  local spanfnbottom = p.spanfnbottom
  local function sbot(i)
    if spanfnbottom then return false end
    local bl = bots[i] and bots[i][#bots[i]]
    return bl and (node.has_attribute(bl, PH) or node.has_attribute(bl, SPAN)) and true or false
  end
  local total_h, textdp = natural(text.head)
  -- 本文の行の標準の深さ（いちばん多い深さ）．本文で終わる段は，最終行の実際の
  -- 深さではなく，この深さでそろえる（ベースラインをそろえるため）
  local linedp = 0
  do
    local cnt, best = {}, 0
    for n in node.traverse_id(HLIST, text.head) do
      if n.list then
        cnt[n.depth] = (cnt[n.depth] or 0) + 1
        if cnt[n.depth] > best then best, linedp = cnt[n.depth], n.depth end
      end
    end
  end
  local topskip = tex.getglue('topskip')
  local SCR = p.scratch

  -- footnote=page：段の最後の垂直の箱の中身が，箱の下端（深さ）より下にはみ出す分
  -- （ページの脚注にかからないよう，段の高さに数える）
  local function excess(list)
    if not fullfn or not list then return 0 end
    local t = node.tail(list)
    while t and t.id == WHATSIT do t = t.prev end
    if t and t.id == VLIST then return math.max(0, vbox_over(t) - t.depth) end
    return 0
  end
  -- ページを組み直すとき（floatgrid）：下のフロートのある段は，フロートの下端を
  -- 段の高さを超えない最後の行の位置（ベースラインに本文の行の深さを足した位置）に
  -- そろえる（段の高さは版面から段抜きのフロートや脚注を除いた高さで，行送りの倍数とは
  -- 限らないので）
  local function gridbot(x)
    if p.fixed and p.floatgrid and p.blskip > 0 and x > topskip + linedp then
      return topskip + math.floor((x - topskip - linedp + 655) / p.blskip) * p.blskip + linedp
    end
    return x
  end
  -- 段の高さhで詰めてみる．入り切れば段ごとの結果を返す
  local function fill_once(h, E)
    tex.setbox(SCR, (vpack(copy_list(text.head))))
    local res = {}
    local ok = true
    for i = 1, N do
      local fl = fl_top[i] + fl_bot[i]
      local function cap(fids)
        if fullfn then
          local hh = math.min(h, colht - curFT)
          if fl_bot[i] > 0 then hh = gridbot(hh) end
          return hh - fl
        end
        local f, fd = fnblock(fids)
        -- 段をまたぐ図のまとまりの段は，まとまりのいちばん高い脚注の分を見込む
        if E and E[i] and E[i] > f then f = E[i] end
        if p.colmode or sbot(i) then
          -- 段の下端の脚注は，最終行のベースラインを本文の最終行のベースラインに
          -- そろえる．本文の最終行の深さと脚注の塊を行送りの倍数に切り上げて
          -- 見込み，端数は脚注の上のfilで吸収する（本文の行を丸ごと減らす）
          if f > 0 then
            f = f + linedp
            if p.blskip > 0 and not p.relaxed then  -- 1回目だけ切り上げる
              f = math.ceil(f / p.blskip - 0.001) * p.blskip
            end
          end
          return h - fl - f
        else
          return math.min(h, colht - f) - fl
        end
      end
      local r = {}
      if i < N or p.fixed then
        local t = cap(fnids(i, {}))
        -- ページを組み直すとき（fixed）：フロートだけの段には本文を入れない．フロートだけで
        -- 段の高さを超える段も，本文を入れずにそのまま組む
        if p.fixed and (t < 0 or (cols[i] and cols[i].fcol)) then t = 0 end
        -- フロートと動かせない脚注だけで段の高さを超える
        if t < 0 then ok = false break end
        local saved = boxlist_copy(SCR)
        for iter = 1, 10 do
          local chunk
          if t > 0 and saved then
            chunk = tex.splitbox(SCR, t, 'exactly')
          end
          local list = chunk and chunk.list
          if chunk then chunk.list = nil; node.free(chunk) end
          if p.floatgrid then snap_chunk(list, topskip, p.blskip) end
          local ids = list and collect_ids(list, {}) or {}
          local nh, nd = natural(list)
          local c2 = cap(fnids(i, ids))
          -- ページを組み直すとき：段の先頭の材料が段の高さより高いと，\vsplitはその前の
          -- 印などの後で切り，段に箱が入らない．ページにほかに何もなく（ブロックも段抜きの
          -- フロートもない），フロートのない段では，その材料までを（はみ出させて）この段に
          -- 入れる．ほかに何かあれば，次のページ（段の高さをいっぱいに使える）へ送る
          if p.fixed and p.pageempty and fl_top[i] + fl_bot[i] == 0 and iter == 1 then
            local hasbox = false
            for q in node.traverse(list) do
              if q.id == HLIST or q.id == VLIST or q.id == RULE then hasbox = true break end
            end
            local rest = tex.getbox(SCR)
            if not hasbox and rest and rest.list then
              -- 切り出した分を戻し，最初の箱の下端までで切り直す
              local head = list
              if head then
                node.tail(head).next = rest.list
                rest.list.prev = node.tail(head)
              else
                head = rest.list
              end
              rest.list = nil
              local need, fb = 0, nil
              for q in node.traverse(head) do
                if q.id == GLUE then need = need + q.width
                elseif q.id == KERN then need = need + q.kern
                elseif q.id == HLIST or q.id == VLIST or q.id == RULE then
                  need = need + q.height + q.depth; fb = q; break
                end
              end
              tex.setbox(SCR, (vpack(head)))
              if fb then
                local chunk = tex.splitbox(SCR, need, 'exactly')
                list = chunk and chunk.list
                if chunk then chunk.list = nil; node.free(chunk) end
                ids = list and collect_ids(list, {}) or {}
                nh, nd = natural(list)
                r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
                break
              end
            end
          end
          local vis = nh + excess(list)
          if vis <= c2 or not list then
            r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
            break
          end
          -- ページを組み直すとき（fixed）：フロートのない段で，分けられない材料1つ
          -- だけで段の高さを超えるときは，どの段にも入らないので，はみ出させて置く
          -- ページにほかに何もないとき（ブロックも段抜きフロートもない）は，1段目に
          -- 最初の分けられない塊をはみ出させて置く（何も置けないページを作ると，
          -- 送り返しが止まらなくなる）
          if p.fixed and p.pageempty and fl_top[i] + fl_bot[i] == 0 then
            local nbox = 0
            for q in node.traverse(list) do
              if q.id == HLIST or q.id == VLIST or q.id == RULE then nbox = nbox + 1 end
            end
            if nbox <= 1 or (p.pageempty and i == 1 and iter == 1) then
              r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
              break
            end
          end
          flush_list(list)
          -- 脚注や行ドリの調整で入り切らない：本文を減らしてやり直す
          local t2 = math.min(c2, t - (vis - c2))
          if iter == 10 or t2 >= t then
            if p.fixed then
              -- ページを組み直すとき：この段は本文を入れず，材料を次の段へ回す
              tex.setbox(SCR, saved and vpack(copy_list(saved)) or nil)
              r.list, r.ids, r.ht, r.dp = nil, {}, 0, 0
              break
            end
            ok = false
            break
          end
          t = t2
          tex.setbox(SCR, saved and vpack(copy_list(saved)) or nil)
        end
        if saved then flush_list(saved) end
        if not ok then break end
      else
        local rest = tex.getbox(SCR)
        local list = rest and rest.list
        if rest then rest.list = nil end
        tex.setbox(SCR, nil)
        if p.floatgrid then snap_chunk(list, topskip, p.blskip) end
        local ids = list and collect_ids(list, {}) or {}
        local nh, nd = natural(list)
        r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
        if nh + excess(list) > cap(fnids(i, ids)) then ok = false end
        -- 最右段に強制改段（\columnbreakなど）が残る：この高さでは段が足りない
        for q in node.traverse_id(PENALTY, list) do
          if q.penalty <= -10000 then ok = false break end
        end
      end
      local f, fd = fnblock(fnids(i, r.ids))
      r.fn, r.fd = f, fd
      r.used = fl_top[i] + r.ht + fl_bot[i] + ((p.colmode or sbot(i)) and f > 0 and (r.dp + f) or 0)
      res[i] = r
      if not ok then break end
    end
    if not ok then
      for _, r in pairs(res) do if r.list then flush_list(r.list) end end
      tex.setbox(SCR, nil)
      return nil
    end
    if p.fixed then
      -- 入り切らなかった本文（次のページへ送り返す）
      local rest = tex.getbox(SCR)
      res.rest = rest and rest.list
      if rest then rest.list = nil end
      tex.setbox(SCR, nil)
    end
    return res
  end

  local function free_res(res)
    for _, r in ipairs(res) do if r.list then flush_list(r.list) end end
    if res.rest then flush_list(res.rest); res.rest = nil end
  end
  local step = 65536

  -- 下に段をまたぐ図がある段のまとまり：段iが属するまとまりの最初の段（なければnil）
  local function spangroups()
    local g = {}
    for i = 1, N do
      local bl = bots[i][#bots[i]]
      local k = bl and node.has_attribute(bl, SPAN)
      if k and k > 1 then
        for j = i, math.min(N, i + k - 1) do g[j] = i end
      end
    end
    return g
  end
  -- spanfootnote=bottomのとき：段をまたぐ図のまとまりの段では，まとまりのいちばん高い
  -- 脚注の分を見込んで詰める（段ごとの見込みEを決めて詰め直す）．res.Gに段ごとの
  -- 見込みを返す
  local function fill(h)
    if not spanfnbottom then return fill_once(h) end
    local g = spangroups()
    if not next(g) then return fill_once(h) end
    local E = {}
    for _ = 1, 6 do
      local res = fill_once(h, E)
      if not res then return nil end
      local G = {}
      for j, c0 in pairs(g) do
        local f = res[j].fn or 0
        if not G[c0] or f > G[c0] then G[c0] = f end
      end
      local changed = false
      for j, c0 in pairs(g) do
        if (E[j] or 0) + 655 < G[c0] then E[j] = G[c0]; changed = true end
      end
      if not changed then
        res.G = {}
        for j, c0 in pairs(g) do res.G[j] = G[c0] end
        return res
      end
      free_res(res)
    end
    return nil
  end

  -- 4. 入り切る最小の高さを探す（いまのフロートの割り振りで）
  local function min_h()
    local allfl = 0
    for i = 1, N do allfl = allfl + fl_top[i] + fl_bot[i] end
    local lo = math.floor((total_h + allfl) / N) - 2 * p.blskip
    if lo < 0 then lo = 0 end
    local function feasible(h)
      local r = fill(h)
      if r then free_res(r) return true end
      return false
    end
    if not feasible(colht) then return nil end
    local a, b = lo, colht  -- bでは入り切る
    while b - a > step do
      local m = math.floor((a + b) / 2)
      if feasible(m) then b = m else a = m end
    end
    -- 入り切るかどうかは高さについて単調とは限らないので，少し下から探し直す
    for h = math.max(lo, b - 4 * step), b, step do
      if feasible(h) then return h end
    end
    return b
  end

  -- フロートの割り振りの候補：番号順を保ち（後のフロートは前のフロートと同じか
  -- 後の段），段に置かれていたフロートは元の段かそれより後の段へ．持ち越された
  -- フロートはどの段でもよい．候補が多すぎるときは，段に置かれていたフロートを
  -- 動かさない
  local assigns = {}
  local function enum(j, minc, cur, fixed)
    if #assigns > 256 then return end
    if j > #F then
      assigns[#assigns + 1] = { table.unpack(cur, 1, #F) }
      return
    end
    local f = F[j]
    local from = math.max(minc, math.min(f.orig, N))
    local to = (fixed and not f.deferred) and from or N
    if fixed and not f.deferred and math.min(f.orig, N) < minc then return end
    -- 段をまたぐフロート：置かれた段に固定する（持ち越されたものは，右端を越えない段）
    if f.span then
      if f.deferred then
        -- 持ち越されたもの：上（正）か下（負）．右端を越えない段
        from, to = math.max(minc, 1), N - f.span + 1
        for c = from, to do
          if f.cantop or not f.canbot then cur[j] = c enum(j + 1, c, cur, fixed) end
          if f.canbot then cur[j] = -c enum(j + 1, c, cur, fixed) end
        end
        return
      else
        if f.orig < minc then return end
        from, to = f.orig, f.orig
      end
    end
    for c = from, to do
      cur[j] = c
      enum(j + 1, c, cur, fixed)
    end
  end
  if not p.fixed then enum(1, 1, {}, false) end
  if #assigns > 64 then
    assigns = {}
    enum(1, 1, {}, true)
  end
  -- 段をまたぐフロートが，同じ位置（上か下）で同じ段にかからないか
  local function span_ok(a)
    local cover = { top = {}, bot = {} }
    for j, f in ipairs(F) do
      if f.span then
        -- 同じ段から同じ段数にまたがるものどうしは積み重ねてよい（またがる段の
        -- あいだで並びが同じになる）
        local pos = f.pos
        if f.deferred then pos = a[j] < 0 and 'bot' or 'top' end
        local c0 = math.abs(a[j])
        local key = c0 .. ':' .. f.span
        for c = c0, c0 + f.span - 1 do
          if c > N or (cover[pos][c] and cover[pos][c] ~= key) then return false end
          cover[pos][c] = key
        end
      end
    end
    return true
  end
  do
    local ok = {}
    for _, a in ipairs(assigns) do if span_ok(a) then ok[#ok + 1] = a end end
    assigns = ok
  end
  local best, besth, bestmoves
  for _, a in ipairs(assigns) do
    set_assign(a)
    local hh = min_h()
    info('  placement %s: %s', table.concat(a, ','), hh and pt(hh) or 'does not fit')
    if hh then
      local moves = 0
      for j, f in ipairs(F) do
        if not f.deferred then moves = moves + math.abs(a[j]) - math.min(f.orig, N) end
      end
      if not besth or hh < besth - step / 2
         or (math.abs(hh - besth) <= step / 2 and moves < bestmoves) then
        best, besth, bestmoves = a, hh, moves
      end
    end
  end
  local h, res = besth, nil
  if best then
    set_assign(best)
    res = fill(h)
  end
  -- ページを組み直すとき（fixed）：フロートは置かれた段のまま，段の高さを版面から
  -- ページの脚注を除いた高さにして詰める．入り切らない本文は次のページへ送り返すので，
  -- その脚注の分だけ段を高くできる（高くしても送り返す本文の脚注が戻らない所まで）
  if p.fixed then
    local a = {}
    for j, f in ipairs(F) do a[j] = math.min(f.orig, N) end
    set_assign(a)
    local function need(r)
      local lists = {}
      for i = 1, N do lists[#lists + 1] = r[i].ids or {} end
      return fullspace(pageids(lists))
    end
    res = fill_once(colht - curFT)
    for _ = 1, 6 do
      if not res then break end
      local nd = need(res)
      if nd >= curFT - 655 then break end
      local save = curFT
      curFT = nd
      local r2 = fill_once(colht - curFT)
      if r2 and need(r2) <= curFT + 655 then
        free_res(res)
        res = r2
      else
        if r2 then free_res(r2) end
        curFT = save
        break
      end
    end
    -- 本文の箱が1つも段に入らなかったとき（版面より高い分けられない箱など）は，
    -- LaTeXが組んだ段割りをそのまま使う（送り返しが止まらなくならないように）
    if res and #F == 0 and p.pageempty then
      local any = false
      for i = 1, N do
        for q in node.traverse(res[i].list) do
          if q.id == HLIST or q.id == VLIST or q.id == RULE then any = true break end
        end
      end
      if not any then
        free_res(res)
        res = {}
        local lists = {}
        for i = 1, N do
          local c = cols[i]
          local t = c and c.text and copy_list(c.text)
          if t then
            t = strip_tail(t, true)
            if i > 1 then t = strip_topskip(t) end
          end
          local r = { list = t, ids = t and collect_ids(t, {}) or {}, fn = 0, fd = 0 }
          r.ht, r.dp = natural(t)
          r.used = r.ht
          res[i] = r
          lists[i] = r.ids
        end
        curFT = fullspace(pageids(lists))
        info('nothing fits; using the columns built by LaTeX')
      end
    end
    h = colht - curFT
  end
  if not res then
    flush_list(text.head)
    for _, id in ipairs(segorder) do flush_list(segs[id].head) end
    drop_dbl()
    for _, f in ipairs(F) do node.free(f.box) end
    M.pool = nil
    if saved_deferred then
      -- 行送りへの切り上げをやめてやり直す
      -- 1回目：脚注の塊の切り上げをやめる．2回目：floatgridもやめる
      M.deferred = saved_deferred
      saved_deferred = nil
      p.relaxed = (p.relaxed or 0) + 1
      if p.relaxed >= 2 then p.floatgrid = false end
      info('does not fit; retrying (%s)', p.relaxed == 1 and 'without rounding footnotes'
        or 'without floatgrid')
      return M.balance(p)
    end
    info('could not balance (material does not fit)')
    return
  end
  drop_saved()
  info('%d float(s) in %d candidate placement(s)', #F, #assigns)

  -- 5. 段の下端をそろえる高さを決める
  -- 段ごとに，自然な高さnat（段の上端から最後の要素の基準線まで）と，その下に
  -- 見かけの上で出る分over（本文の最終行の深さや，箱の中身が下にはみ出す分）を
  -- 求め，見かけの下端nat + overを全段でそろえる．
  -- ・本文で終わる段：最終行の字面の下端がそろう
  -- ・下のフロートで終わる段：本文の最終行の深さも積まれるのでnatに数える
  -- ・段下端の脚注で終わる段：脚注の最終行の基準線までをnatとする
  local function measure(res)
    local nat, over = {}, {}
    for i = 1, N do
      local r = res[i]
      local hasbot = #bots[i] > 0
      -- 下に段をまたぐフロート（場所取り）がある段：段下端の脚注はその上に置くので，
      -- 段は下のフロートで終わる
      local spanbot = false
      do
        local bl = bots[i][#bots[i]]
        if bl and (node.has_attribute(bl, PH) or node.has_attribute(bl, SPAN)) then spanbot = true end
      end
      if r.fn > 0 and spanbot and not spanfnbottom then
        -- （脚注の最終行の深さr.fdも数える．脚注の後に\textfloatsepとフロートが続く）
        nat[i] = fl_top[i] + (r.list and r.ht + r.dp or 0) + r.fn + r.fd + fl_bot[i]
        over[i] = 0
      elseif p.colmode and math.max(r.fn, res.G and res.G[i] or 0) > 0 then
        -- 段下端の脚注はfilで段の下端に付くので，本文（と下のフロート）の後に
        -- 脚注が収まる最初の行の位置（字面の下端）をこの段の下端とみなす
        -- 脚注の最終行のベースラインを，本文の後で脚注が収まる最初の行の位置に置く
        -- 本文の後にグルーなどが残っていれば（最後の箱の後のアキ），それも含める
        local B = fl_top[i] + (r.list and math.max(lastbase(r.list), r.ht) or 0)
        local need = (r.list and r.dp or 0) + fl_bot[i] + math.max(r.fn, res.G and res.G[i] or 0)
        if p.blskip > 0 and r.list then
          -- 段の先頭の行が\topskipより高い（脚注の合印の付いた行など）と，本文の
          -- 行が行送りの位置からわずかに下がる．行送りの位置で見て，下がった分は
          -- 脚注の上のアキから差し引く（そうしないと，この段だけわずかに高いとみなし，
          -- 段の高さを上げてしまう）
          local lb = lastbase(r.list)
          local d = lb - (topskip + math.floor((lb - topskip) / p.blskip + 0.5) * p.blskip)
          if d > 0 and d < 65536 then B, need = B - d, need + d end
        end
        if p.blskip > 0 then
          local m = math.max(0, math.ceil(need / p.blskip - 0.001))
          nat[i], over[i] = B + m * p.blskip, linedp
        else
          nat[i], over[i] = B + need, linedp
        end
        -- 行送りの倍数に切り上げた分で段の高さを超えるときは，段の下端で止める
        -- （脚注はfilで段の下端に付く）
        if nat[i] > colht and B + need <= colht then nat[i] = colht end
      elseif r.ht == 0 and (#tops[i] + #bots[i]) > 0 and not (p.colmode and r.fn > 0) then
        -- フロートだけの段：フロートの下端まで（後ろのアキは数えない）
        local t = 0
        for j, f in ipairs(tops[i]) do t = t + f.height + f.depth + (j > 1 and floatsep or 0) end
        for j, f in ipairs(bots[i]) do
          t = t + f.height + f.depth + ((j > 1 or #tops[i] > 0) and floatsep or 0)
        end
        -- 下のフロートもあれば，組むとおり（上の並び，\textfloatsep，下の並び）に数える
        if #bots[i] > 0 then t = fl_top[i] + fl_bot[i] end
        nat[i], over[i] = t, 0
      elseif hasbot then
        nat[i], over[i] = fl_top[i] + r.ht + (r.list and r.dp or 0) + fl_bot[i], 0
      else
        nat[i], over[i] = fl_top[i] + r.ht, overhang(r.list)
        -- 本文の行で終わるなら，最後の行のベースライン（後ろのアキを除く）と
        -- 標準の深さで見る
        local t = r.list and node.tail(r.list)
        while t and (is_discardable(t) or t.id == WHATSIT) do t = t.prev end
        if t and t.id == HLIST and not is_intext(t) then
          nat[i] = fl_top[i] + lastbase(r.list)
          over[i] = linedp
        end
        -- 本文中のフロートで終わる段は，次の格子の字面の下端までを見かけとする
        if p.floatgrid and p.blskip > 0 and ends_intext(r.list) then
          local pos = nat[i] + over[i]
          local k = math.ceil((pos - topskip - linedp - 655) / p.blskip)
          over[i] = over[i] + math.max(0, topskip + k * p.blskip + linedp - pos)
        elseif ends_intext(r.list) then
          -- floatgridでないとき：フロートの後のアキ（\intextsep）は見かけに数えない
          local t, trail = node.tail(r.list), 0
          while t and (is_discardable(t) or t.id == WHATSIT) do
            if t.id == GLUE then trail = trail + t.width
            elseif t.id == KERN then trail = trail + t.kern end
            t = t.prev
          end
          nat[i] = nat[i] - trail
        end
      end
    end
    return nat, over
  end
  -- 下端がそろわない配分か：最右段が他のどの段よりも高い，または，本文だけの
  -- 満杯の段より高い段があって，フロートまわりのグルーの縮みでも吸収できない
  local function misaligned(res, nat, over)
    if N < 2 then return false end
    local m, textvis = 0, nil
    for i = 1, N - 1 do
      local v = nat[i] + over[i]
      m = math.max(m, v)
      if fl_top[i] + fl_bot[i] == 0 and res[i].list then
        textvis = math.max(textvis or 0, v)
      end
    end
    if nat[N] + over[N] > m + 655 then return true end  -- 0.01pt
    -- 途中の段（後ろに中身のある段がある）が本文だけの満杯の段より明らかに短い
    if textvis then
      for i = 1, N - 1 do
        local later = false
        for k = i + 1, N do if res[k].ht > 0 or #tops[k] + #bots[k] > 0 then later = true end end
        if later and res[i].ht > 0 and nat[i] + over[i] < textvis - p.blskip / 2 then
          return true
        end
      end
    end
    if textvis then
      for i = 1, N do
        if nat[i] + over[i] - fl_shrink[i] > textvis + 655 then return true end
      end
    end
    return false
  end
  local function free_res(res)
    for _, r in ipairs(res) do if r.list then flush_list(r.list) end end
  end
  local nat, over = measure(res)
  -- 下端がそろわない配分なら（脚注やフロートで最右段やフロートのある段だけが
  -- 高くなったとき），段の高さを上げてそろう配分を探す（最右段は短くてよいが，
  -- 他の段より高くはしない）．段の高さいっぱいまで探す
  if not p.fixed and misaligned(res, nat, over) then
    -- footnote=page：ページの脚注の分は上げられない（最終行のベースラインまで．
    -- 行の深さは脚注の上のアキに出てよい）
    local hh, hmax = h + step, fullfn and (colht - curFT + linedp) or colht
    while hh <= hmax do
      local r2 = fill(hh)
      if r2 then
        local n2, o2 = measure(r2)
        if not misaligned(r2, n2, o2) then
          free_res(res)
          res, h, nat, over = r2, hh, n2, o2
          break
        end
        free_res(r2)
      end
      hh = hh + step
    end
  end
  -- 見かけの下端の最大値にそろえる．本文だけの満杯の段があれば，行の位置が
  -- そろうようにその段を基準にし，フロートのある段はフロートまわりのグルーの
  -- 縮みで吸収する
  local maxvis, textvis = 0, nil
  for i = 1, N do
    local v = nat[i] + over[i]
    if v > maxvis then maxvis = v end
    if i < N and fl_top[i] + fl_bot[i] == 0 and res[i].list then
      if not textvis or v > textvis then textvis = v end
    end
  end
  local bottom = maxvis
  if textvis and textvis < maxvis then
    local ok = true
    for i = 1, N do
      if nat[i] + over[i] - fl_shrink[i] > textvis then ok = false end
    end
    if ok then bottom = textvis end
  end
  if not p.fixed then h = bottom end
  -- footnote=page：揃えた段組の見かけの下端は，最終行のベースラインが版面からページの
  -- 脚注の領域を除いた高さに来る所まで（最後の箱の中身が下にはみ出す分などで超えない
  -- ように）
  if fullfn and h > colht - curFT + linedp then h = colht - curFT + linedp end
  -- 揃えた段組の最終行のベースライン：本文で終わって下端に達した段があれば
  -- その最終行，なければ本文の行の深さだけ下端から上
  local base
  for i = 1, N do
    local endstext = res[i].list and not (#bots[i] > 0)
                     and not ((p.colmode or sbot(i)) and res[i].fn > 0)
    if not base and endstext and math.abs(nat[i] + over[i] - h) < 655 then
      base = h - over[i]
    end
  end
  if not base then
    local d = 0
    for i = 1, N do
      if res[i].list and res[i].dp > d then d = res[i].dp end
    end
    base = h - d
  end
  if p.fixed then
    info('rebuilt page with full-width footnotes at %s (colht %s, footnotes %s)',
      pt(h), pt(colht), pt(curFT))
  else
    info('balanced at %s (colht %s, text %s)', pt(h), pt(colht), pt(total_h))
  end
  for i = 1, N do
    local r = res[i]
    info('  column %d: text %s+%s, floats %s (top %d, bottom %d), footnotes %s, bottom %s+%s',
      i, pt(r.ht), pt(r.dp), pt(fl_top[i] + fl_bot[i]), #tops[i],
      #bots[i], pt(r.fn), pt(nat[i]), pt(over[i]))
  end

  -- 中身のある最後の段（その後の段が空なら，最右段と同じく短くてよい）
  local lastfull = N
  while lastfull > 1 and res[lastfull].ht == 0 and #tops[lastfull] + #bots[lastfull] == 0
        and res[lastfull].fn == 0 do
    lastfull = lastfull - 1
  end

  -- 6. 段を組み立てる
  local function figrule(n)
    return boxlist_copy(n)
  end
  M.out = {}
  M.rule = {}
  local colinfo = {}
  local usefnpage = false
  for i = 1, N do
    local r = res[i]
    local l = newlist()
    -- 段間罫のために，段の中の本文・脚注でない要素（フロートと罫）を覚えておく
    local skip, botset = {}, {}
    if #tops[i] > 0 then
      -- floatgridでは上のフロートまわりのアキを伸縮させず，行送りの倍数に
      -- 切り上げた分を本文の前に足す
      local function sep(name)
        if p.floatgrid then return mkglue((tex.getglue(name))) end  -- 自然長だけ
        return regglue(name)
      end
      for j, f in ipairs(tops[i]) do
        if j > 1 then append(l, sep('floatsep')) end
        append(l, f)
        skip[node.direct.todirect(f)] = true
      end
      do
        local fr = figrule(p.topfig)
        for q in node.traverse(fr) do skip[node.direct.todirect(q)] = true end
        append(l, fr)
      end
      append(l, sep('textfloatsep'))
      if ext_top[i] > 0 then append(l, mkglue(ext_top[i])) end
    end
    append(l, r.list)
    r.list = nil
    local ids = fnids(i, r.ids)
    -- 脚注の並び（脚注の上のアキ，脚注罫，脚注）
    local fl = newlist()
    if #ids > 0 then
      append(fl, regglue(p.footins))
      append(fl, boxlist_copy(p.fnrule))
      for _, id in ipairs(ids) do
        append(fl, segs[id].head)
        segs[id].head = nil
      end
    end
    -- 段間罫を避ける，段の中の脚注の領域の高さ（段の下端の脚注のとき）
    -- 段の中の脚注の領域の高さ（段の下端の脚注のとき）．fnnotesは\skip\footinsを除いた分
    local fnarea, fnnotes = 0, 0
    if (p.colmode or sbot(i)) and fl.head then
      fnarea = natural(fl.head)
      fnnotes = fnarea - (tex.getglue(p.footins))
    end
    -- 段の高さ：見かけの下端がそろう位置．版面下端の脚注があれば，組み上げた
    -- 脚注の並びの実際の高さの分だけ上で止める
    local target = h - over[i]
    if p.fixed then
      target = h
      if #bots[i] > 0 then target = gridbot(h) end
    end
    local pushed = false
    if not (p.colmode or sbot(i)) and fl.head then
      local fnh = natural(fl.head)
      if colht - fnh < target then target, pushed = colht - fnh, true end
    end
    -- 段の高さに届かない最右段と，版面下端の脚注に押された段と，（段の高さを
    -- 上げても配分をそろえられなかったときの）短い途中の段（次の段の先頭の材料
    -- （本文中のフロート，長い脚注の付いた行など）が入らなかった）は，グルーを
    -- 伸ばさずに下を空ける．それ以外の段はグルーを伸ばして下端をそろえる
    local blocked = false
    if i < lastfull and res[i + 1] and (res[i + 1].ht > 0 or #tops[i + 1] + #bots[i + 1] > 0) then
      blocked = true
    end
    -- 強制改段（\columnbreakなど）で終わる段：改段の前の\vfilで下を空ける
    local colbreak = false
    do
      local t = l.tail
      while t and (t.id == WHATSIT or t.id == PENALTY) do t = t.prev end
      colbreak = t and t.id == GLUE and t.stretch_order > 0 or false
    end
    local ragged = (i >= lastfull or pushed or blocked) and target - nat[i] > p.blskip / 2
    -- ページを組み直すとき：入り切らない本文がなければ（本文が足りない），中身のある
    -- 最後の段は下を空ける．それ以外の段はグルーを伸ばして段の高さいっぱいに組む
    if p.fixed then
      ragged = ((i >= lastfull and not res.rest) or blocked) and target - nat[i] > p.blskip / 2
    end
    -- 本文の下のアキ：下フロートと（段下端モードの）脚注は段の下端に付ける
    local gallow = res.G and res.G[i] or 0
    if ragged or ((p.colmode or sbot(i)) and (#ids > 0 or gallow > 0)) then
      append(l, filglue())
    elseif p.fixed and #bots[i] == 0 then
      -- LaTeXの段と同じく，最後の行のベースラインを段の下端に置く（深さは下に出す）．
      -- 段の下の\@textbottomも足す
      local t = l.tail
      if t and (t.id == HLIST or t.id == VLIST) and t.depth ~= 0 then
        append(l, node.new(KERN)); l.tail.kern = -t.depth
      end
      if p.textbottom then append(l, boxlist_copy(p.textbottom)) end
    end
    -- 下に段をまたぐフロート（場所取り）がある段では，段下端の脚注をフロートの上に
    -- 置く（またがる段のあいだでフロートの位置がそろうように）
    local spanbot = false
    do
      local bl = bots[i][#bots[i]]
      if bl and (node.has_attribute(bl, PH) or node.has_attribute(bl, SPAN)) then spanbot = true end
    end
    if spanbot and fl.head and not spanfnbottom then
      append(l, fl.head)
      fl.head = nil
    end
    if #bots[i] > 0 then
      if ext_bot[i] > 0 then append(l, mkglue(ext_bot[i])) end
      append(l, regglue('textfloatsep'))
      do
        local fr = figrule(p.botfig)
        for q in node.traverse(fr) do
          local d = node.direct.todirect(q)
          skip[d] = true; botset[d] = true
        end
        append(l, fr)
      end
      for j, f in ipairs(bots[i]) do
        if j > 1 then append(l, regglue('floatsep')) end
        append(l, f)
        local d = node.direct.todirect(f)
        skip[d] = true; botset[d] = true
      end
    end
    local body
    local gapadd = 0  -- 図の下に足したアキ（脚注の分．見かけの下端の報告に使う）
    if p.colmode then
      -- 段をまたぐ図のまとまりの段：図の下端をそろえるため，脚注との間を空ける
      if gallow > 0 then
        local own = (#ids > 0) and (fnblock(ids)) or 0
        if gallow - own > 0 then gapadd = gallow - own; append(l, mkglue(gapadd)) end
      end
      append(l, fl.head)
      body = vpack(l.head or node.new(GLUE), target, 'exactly')  -- 空の段もある
    else
      if fl.head then usefnpage = true end
      body = vpack(l.head or node.new(GLUE), target, 'exactly')
      if fl.head then
        local o = newlist()
        append(o, body)
        append(o, filglue())
        append(o, fl.head)
        body = vpack(o.head, colht, 'exactly')
      end
    end
    if M.debug and not p.fixed then
      -- 実際に置かれた見かけの下端（グルーが伸びて届いたか）
      local b = body
      if fl.head and not p.colmode then b = body.list end
      -- 段下端の脚注はfilで段の下端に付けてある
      local filfn = (p.colmode or sbot(i)) and #ids > 0
      local placed = (b.glue_sign ~= 0 and (b.glue_order == 0 or filfn)) and target or nat[i]
      if filfn then placed = target end
      -- 組み上げた箱を実際にたどって，最後に見える要素の下端を求める
      -- （本文の行はベースライン＋標準の深さ，脚注の行は実際の深さ）
      local function vis(box, y0)
        local y, last = y0, nil
        for n in node.traverse(box.list) do
          local id = n.id
          if id == GLUE then y = y + node.effective_glue(n, box)
          elseif id == KERN then y = y + n.kern
          elseif id == HLIST or id == VLIST or id == nodeid('rule') then
            local base = y + n.height
            if is_intext(n) then
              -- 本文中のフロートや高い箱は，その領域が行き着く次の行の字面の下端まで
              last = base + (n.id == VLIST and vbox_over(n) or n.depth)
              if p.floatgrid and p.blskip > 0 then
                local k = math.ceil((last - topskip - linedp - 655) / p.blskip)
                last = math.max(last, topskip + k * p.blskip + linedp)
              end
            elseif id == HLIST and n.list then
              last = base + linedp  -- 行はベースラインでそろえる
            elseif n.height + n.depth > 0 then
              last = base + (id == VLIST and vbox_over(n) or n.depth)
            end
            y = base + n.depth
          end
        end
        return last or y0
      end
      if os.getenv('EVENEND_TRACE') then  -- 調査用：段の中の要素の位置
        local y, out = 0, {}
        local tb = body
        if not p.colmode and fl.head and body.list and body.list.id == VLIST then tb = body.list end
        for n in node.traverse(tb.list) do
          if n.id == GLUE then y = y + node.effective_glue(n, tb); out[#out + 1] = string.format('g%.2f', n.width / 65536)
          elseif n.id == KERN then y = y + n.kern; out[#out + 1] = string.format('k%.2f', n.kern / 65536)
          elseif n.id == HLIST or n.id == VLIST then
            y = y + n.height
            out[#out + 1] = string.format('%s@%.2f(%.1f+%.1f%s)', n.id == HLIST and 'L' or (is_intext(n) and 'F' or 'V'), y / 65536, n.height / 65536, n.depth / 65536, is_intext(n) and 'I' or '')
            y = y + n.depth
          end
        end
        info('    trace column %d: %s', i, table.concat(out, ' '))
      end
      -- 版面下端の脚注があるときは，脚注を除いた本文の箱（外側の箱の最初の要素）を測る
      local geo
      if not p.colmode and fl.head and body.list and body.list.id == VLIST then
        geo = vis(body.list, 0)
      else
        geo = vis(body, 0)
      end
      placed = geo - over[i]
      -- 脚注のない段で，図の下に脚注の分のアキを足して下端をそろえた（\vfilで段の
      -- 下端に付けてある）
      if #ids == 0 and gapadd > 0 then placed = target end
      if ragged and not filfn and gapadd == 0 then placed = nat[i] end
      local floatsonly = r.ht == 0 and (#tops[i] + #bots[i]) > 0
      -- 伸ばせるグルーがなくて届かない（行送りの位置にそろわない組版の限界）
      local nostretch = not ragged and not filfn and b.glue_sign ~= 1 and placed < target - 655
      -- 段の中身が段の高さを超える（段いっぱいの分割できない箱など）
      local overfull = nat[i] + over[i] > colht + 655
      -- footnote=page：段の高さをページの脚注の上までに抑えたので，見かけの下端
      -- （本文中の箱の後の行送りの位置など）がそれより下になる
      local capped = fullfn and placed + over[i] > h + 655
      info('  column %d placed %s%s', i, pt(placed + over[i]),
        overfull and ' (overfull)' or capped and ' (footnotes)' or
        pushed and ' (pushed)' or floatsonly and ' (floats only)'
        or colbreak and ' (column break)'
        or (blocked and (ragged or nostretch)) and ' (blocked)'
        or ragged and ' (ragged)' or nostretch and ' (no stretch)' or '')
    end
    -- 段間罫：段をまたぐフロートの場所取りがこの段にあれば，罫はフロートの所を避け，
    -- 段間の両側の本文（と脚注）の行のある範囲に引く．組み上げた段をたどって，下の
    -- フロートより前（本文と，その上に置いた脚注）と後（spanfootnote=bottomの脚注）の，
    -- 最初の行の上端と最後の行の下端を求める
    do
      local inner = body
      if not p.colmode and fl.head and body.list and body.list.id == VLIST then inner = body.list end
      local y, seenbot = 0, false
      local pt0, pb0, pt1, pb1
      for q in node.traverse(inner.list) do
        local id = q.id
        if id == GLUE then y = y + node.effective_glue(q, inner)
        elseif id == KERN then y = y + q.kern
        elseif id == HLIST or id == VLIST or id == RULE then
          local rec = { q = q, y = y }
          local d = node.direct.todirect(q)
          if skip[d] then
            if botset[d] then seenbot = true end
          elseif q.height + q.depth > 0 then
            if not seenbot then pt0 = pt0 or rec; pb0 = rec
            else pt1 = pt1 or rec; pb1 = rec end
          end
          y = y + q.height + q.depth  -- 次の要素へは箱の大きさで進む
        end
      end
      local t1, bl = tops[i][1], bots[i][#bots[i]]
      colinfo[i] = {
        top = pt0, bot = pb0, fntop = pt1, fnbot = pb1,  -- 罫の端は要るときに測る
        ph_top = t1 and node.has_attribute(t1, PH) and true or false,
        ph_bot = bl and node.has_attribute(bl, PH) and true or false,
      }
      local function lo(x, y2) if x and y2 then return math.min(x, y2) end return x or y2 end
      local function hi(x, y2) if x and y2 then return math.max(x, y2) end return x or y2 end
      local rtop, rend, r2top, r2end = 0, 0, 0, 0
      local a, c = colinfo[i - 1], colinfo[i]
      if a and c.ph_top then rtop = lo(edge_top(a.top), edge_top(c.top)) or 0 end
      if a and c.ph_bot then
        rend = hi(edge_bot(a.bot), edge_bot(c.bot)) or 0
        -- spanfootnote=bottom：図の下の脚注の横にも引く（脚注の下端まで）
        r2top = lo(edge_top(a.fntop), edge_top(c.fntop)) or 0
        r2end = hi(edge_bot(a.fnbot), edge_bot(c.fnbot)) or 0
      end
      M.rule[i] = { rtop, rend, r2top, r2end }
    end
    local o = newlist()
    append(o, body)
    append(o, vssglue())
    M.out[i] = vpack(o.head, (p.block or fullfn) and h or colht, 'exactly')
  end
  -- フロートの箱は段に入れたので，M.resetで片付けない
  M.pool = nil
  -- 持ち越された段抜きフロートの並び（揃えた段組の下に置く）
  if #dblfloats > 0 then
    local l = newlist()
    append(l, regglue('dbltextfloatsep'))
    for j, f in ipairs(dblfloats) do
      if j > 1 then append(l, regglue('dblfloatsep')) end
      append(l, f)
    end
    M.dblbox = vpack(l.head)
    dblfloats = {}
  end
  -- footnote=page：ページの脚注（全幅）．組み直したページで入り切らなかった本文は，
  -- その脚注を\insertに戻して付け，次のページへ送り返す
  if fullfn then
    local lists = {}
    for i = 1, N do lists[i] = res[i].ids or {} end
    local fl = newlist()
    for _, id in ipairs(pageids(lists)) do
      if segs[id].head then append(fl, segs[id].head); segs[id].head = nil end
    end
    M.fnlist = fl.head
    if p.fixed and res.rest then
      M.push = make_push(res.rest, segs, p)
      res.rest = nil
    end
  end
  -- 使われなかった脚注断片（本来は無いはず）を片付ける
  for _, id in ipairs(segorder) do
    if segs[id].head then flush_list(segs[id].head) end
  end
  flush_list(text.head)
  tex.setdimen('global', 'evenend@ruleht', usefnpage and colht or h)
  local colboxht = (p.block or fullfn) and h or colht
  tex.setdimen('global', 'evenend@colboxht', colboxht)
  tex.setdimen('global', 'evenend@rowht', colboxht + dblh)
  -- 段抜きフロートで終わるときは，その下端から本文の行の深さだけ上を最終行とみなす
  if dblh > 0 then
    local d = 0
    for i = 1, N do if res[i].list and res[i].dp > d then d = res[i].dp end end
    base = colboxht + dblh - d
  end
  tex.setdimen('global', 'evenend@baseline', base + headshift)
  tex.setdimen('global', 'evenend@rowht', colboxht + dblh + headshift)
  tex.setdimen('global', 'evenend@headshift', headshift)
  tex.setdimen('global', 'evenend@height', h)
  tex.setcount('global', 'evenend@status', 1)
end

-- 段抜きフロートの並び（なければ空）を箱レジスタnに入れる
function M.getdbl(n)
  tex.setbox(n, M.dblbox)
  M.dblbox = nil
end

-- ページの本文（箱src）の中のマークを，読む順序（ブロックは上から，段は左から，
-- 段の中は上から）に集め，写しを並べた垂直の箱を箱レジスタdstに入れる
local MARK = nodeid('mark')
function M.collectmarks(src, dst)
  local l = newlist()
  local function walk(head)
    for n in node.traverse(head) do
      if n.id == MARK then
        append(l, node.copy(n))
      elseif (n.id == HLIST or n.id == VLIST) and n.list then
        walk(n.list)
      end
    end
  end
  local b = tex.getbox(src)
  if b and b.list then walk(b.list) end
  tex.setbox(dst, (vpack(l.head or node.new(GLUE))))
end

-- 組み上がったi段目を箱レジスタnに入れる
function M.getcolumn(i, n)
  local b = M.out and M.out[i]
  if b then M.out[i] = nil end
  local r = M.rule and M.rule[i] or { 0, 0, 0, 0 }
  tex.setdimen('global', 'evenend@rtop', r[1])
  tex.setdimen('global', 'evenend@rend', r[2])
  tex.setdimen('global', 'evenend@rtwotop', r[3] or 0)
  tex.setdimen('global', 'evenend@rtwoend', r[4] or 0)
  tex.setbox(n, b)
end

-- ---------------------------------------------------------------------
-- 箱の中の段組（tcolorboxなど．出力ルーチンを使わない）
-- 段幅で組んだ中身（箱p.content）をN段に分け，揃えた行を箱p.outに入れる．
-- 各段の1行目のベースラインをそろえ（段の上端からの位置T），最終行のベースラインで
-- 下端をそろえる．最右段（と\columnbreakで終わる段）は下を空けてよい
local SPLITTOPSKIP = 11  -- glueのsubtype：\splittopskip
function M.boxbalance(p)
  local N = p.N
  local src = tex.getbox(p.content)
  local list = src and src.list
  if src then src.list = nil end
  tex.setbox(p.content, nil)
  list = strip_tail(list, true)
  tex.setdimen('global', 'evenend@boxtop', 0)
  tex.setdimen('global', 'evenend@boxfirst', 0)
  -- 箱や罫のない中身（空の環境）は出さない
  local hasbox = false
  for n in node.traverse(list) do
    if n.id == HLIST or n.id == VLIST or n.id == RULE then hasbox = true break end
  end
  if not hasbox then
    if list then flush_list(list) end
    tex.setbox('global', p.out, nil)
    return
  end
  local SCR = p.scratch

  -- 段の高さhで分ける．入り切れば各段の中身（リスト）を返す
  local function split(h)
    tex.setbox(SCR, (vpack(copy_list(list))))
    local parts = {}
    for i = 1, N - 1 do
      local b = tex.getbox(SCR) and tex.splitbox(SCR, h, 'exactly')
      parts[i] = b and b.list or false
      if b then b.list = nil; node.free(b) end
    end
    local rest = tex.getbox(SCR)
    parts[N] = rest and rest.list or false
    if rest then rest.list = nil end
    tex.setbox(SCR, nil)
    local ok = true
    if parts[N] then
      if natural(parts[N]) > h then ok = false end
      -- 最右段に強制改段（\columnbreak）が残る：この高さでは段が足りない
      for q in node.traverse_id(PENALTY, parts[N]) do
        if q.penalty <= -10000 then ok = false break end
      end
    end
    return parts, ok
  end
  local function free(parts)
    for i = 1, N do if parts[i] then flush_list(parts[i]) end end
  end

  -- 入り切る最小の高さ
  local total = natural(list)
  local lo, hi = 0, total
  local parts, ok = split(hi)
  if not ok then
    -- 強制改段が多すぎる：分けずに1段目にすべて入れる
    free(parts)
    parts = { list }
    for i = 2, N do parts[i] = false end
    list = nil
  else
    free(parts)
    local step = 65536 / 10  -- 0.1pt
    while hi - lo > step do
      local m = math.floor((lo + hi) / 2)
      local ps, o = split(m)
      free(ps)
      if o then hi = m else lo = m end
    end
    parts = split(hi)
  end

  -- 各段の先頭：\splittopskipのグルーを除き，1行目のベースラインを段の上端からTの
  -- 位置にそろえる．各段の最終行のベースラインの位置natと，その最大値Hを求める
  local topskip = p.topskip
  local T, F, nat, H, lastfull
  local function prepare(parts)
    T, F = topskip, 0  -- F：1行目の高さの最大値
    local first = {}
    for i = 1, N do
      local l = parts[i]
      if l then
        local n = l
        while n and n.id ~= HLIST and n.id ~= VLIST and n.id ~= RULE do
          local nx = n.next
          if n.id == GLUE and (n.subtype == SPLITTOPSKIP or n.subtype == TOPSKIP) then
            l = node.remove(l, n)
            node.free(n)
          end
          n = nx
        end
        parts[i] = l
        first[i] = n
        if n and n.height > T then T = n.height end
        if n and n.height > F then F = n.height end
      end
    end
    for i = 1, N do
      if first[i] then
        local g = mkglue(T - first[i].height)
        parts[i] = node.insert_before(parts[i], first[i], g)
      end
    end
    H, nat = 0, {}
    for i = 1, N do
      nat[i] = parts[i] and natural(parts[i]) or 0
      if nat[i] > H then H = nat[i] end
    end
    -- 中身のある最後の段
    lastfull = N
    while lastfull > 1 and not parts[lastfull] do lastfull = lastfull - 1 end
  end
  -- 最右段より前の段が，伸ばせるグルーもなく最終行の位置に届かないか
  local function misaligned(parts)
    for i = 1, lastfull - 1 do
      if parts[i] and nat[i] < H - 655 then
        local stretch = false
        for g in node.traverse_id(GLUE, parts[i]) do
          if g.stretch > 0 then stretch = true break end
        end
        if not stretch then return true end
      end
    end
    return false
  end
  prepare(parts)
  -- 届かない段があれば（行の途中の分割を避けて1行早く分けたときなど），段の高さを
  -- 上げて，そろう分け方を探す
  if list and misaligned(parts) then
    local step = 65536
    for hh = hi + step, total, step do
      local ps, o = split(hh)
      if o then
        local saveT, saveF, savenat, saveH, savelast = T, F, nat, H, lastfull
        prepare(ps)
        if not misaligned(ps) then
          free(parts)
          parts = ps
          break
        end
        T, F, nat, H, lastfull = saveT, saveF, savenat, saveH, savelast
      end
      free(ps)
    end
  end
  if list then flush_list(list) end
  list = nil

  local row = newlist()
  local cw, sep, rule = p.cw, p.sep, p.rule
  local maxdp = 0
  for i = 1, N do
    if i > 1 then
      local k1 = node.new(KERN); k1.kern = math.floor((sep - rule) / 2)
      append(row, k1)
      if rule > 0 then
        local r = node.new(RULE)
        r.width, r.height, r.depth = rule, H, 0
        append(row, r)
      end
      local k2 = node.new(KERN); k2.kern = sep - rule - k1.kern
      append(row, k2)
    end
    local l = parts[i]
    local col
    if not l then
      col = vpack(mkglue(0), H, 'exactly')
    else
      -- 下端をそろえる段はグルーを伸ばす．最右段などの短い段は下を空ける
      local ragged = (i >= lastfull) and (H - nat[i] > p.blskip / 2)
      if ragged then
        local t = node.tail(l)
        node.insert_after(l, t, vssglue())
      end
      col = vpack(l, H, 'exactly')
      -- 下端がそろったか（伸ばせるグルーがなくて届かない段）
      local short = not ragged and H - nat[i] > 655 and col.glue_sign ~= 1
      info('  box column %d: %s%s', i, pt(nat[i]),
        ragged and ' (ragged)' or short and ' (no stretch)' or '')
    end
    col.width = cw
    if col.depth > maxdp then maxdp = col.depth end
    append(row, col)
  end
  local out = node.hpack(row.head)
  out.height, out.depth = H, maxdp
  tex.setbox('global', p.out, out)
  tex.setdimen('global', 'evenend@boxtop', T)
  tex.setdimen('global', 'evenend@boxfirst', F)
  info('box balanced at %s (%d columns, first baseline %s)', pt(H), N, pt(T))
end

return M
