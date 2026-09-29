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
local USERDEF     = node.subtype('user_defined')
local TOPSKIP     = 10   -- glueのsubtype：\topskip
local USER_ID     = 0x65766E64  -- 'evnd'

local copy_list   = node.copy_list
local flush_list  = node.flush_list
local vpack       = node.vpack
local has_attr    = node.has_attribute

-- 本文中のフロート（[h]）の印
local INTEXT = luatexbase.new_attribute('evenend@intext')

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

function M.addfloat(where, boxnum)
  local c = M.cols[#M.cols]
  local b = tex.getbox(boxnum)
  if c and b then
    table.insert(c[where], node.copy(b))
  end
end

-- まだ出ていない（持ち越された）フロート：kindは'col'（段内）か'dbl'（段抜き）
M.deferred = { col = {}, dbl = {} }
function M.adddeferred(kind, boxnum)
  local b = tex.getbox(boxnum)
  if b then table.insert(M.deferred[kind], node.copy(b)) end
end

-- フロートだけの段（LaTeXが\@tryfcolumnで作る）：その中身を自然な高さに組み直して
-- 上のフロートとして取り込む
function M.capturefcol(boxnum)
  local b = tex.getbox(boxnum)
  local c = { top = {}, bot = {} }
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
        local function rigid(g) if g then node.setglue(g, g.width, 0, 0, 0, 0) end end
        rigid(gafter)
        do
          local m = n.prev
          while m and not is_line(m) and m.id ~= VLIST do
            if m.id == GLUE then rigid(m); break end
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
function M.balance(p)
  local cols = M.cols
  local N, colht = p.N, p.colht
  if p.block then p.colmode = true end
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
    local r = {}
    for _, id in ipairs(orphans[i]) do r[#r + 1] = id end
    for _, id in ipairs(ids) do
      if segs[id] and anchored[id] then r[#r + 1] = id end
    end
    return r
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
  local F = {}
  for k, c in ipairs(cols) do
    for _, f in ipairs(c.top) do F[#F + 1] = { box = node.copy(f), pos = 'top', orig = k } end
    for _, f in ipairs(c.bot) do F[#F + 1] = { box = node.copy(f), pos = 'bot', orig = k } end
  end
  for _, f in ipairs(M.deferred.col) do
    F[#F + 1] = { box = f, pos = 'top', orig = 1, deferred = true }
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
    for j, f in ipairs(F) do
      table.insert(f.pos == 'top' and tops[assign[j]] or bots[assign[j]], f.box)
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

  -- 段の高さhで詰めてみる．入り切れば段ごとの結果を返す
  local function fill(h)
    tex.setbox(SCR, (vpack(copy_list(text.head))))
    local res = {}
    local ok = true
    for i = 1, N do
      local fl = fl_top[i] + fl_bot[i]
      local function cap(fids)
        local f, fd = fnblock(fids)
        if p.colmode then
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
      if i < N then
        local t = cap(fnids(i, {}))
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
          if nh <= c2 or not list then
            r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
            break
          end
          flush_list(list)
          -- 脚注や行ドリの調整で入り切らない：本文を減らしてやり直す
          local t2 = math.min(c2, t - (nh - c2))
          if iter == 10 or t2 >= t then
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
        if nh > cap(fnids(i, ids)) then ok = false end
        -- 最右段に強制改段（\columnbreakなど）が残る：この高さでは段が足りない
        for q in node.traverse_id(PENALTY, list) do
          if q.penalty <= -10000 then ok = false break end
        end
      end
      local f, fd = fnblock(fnids(i, r.ids))
      r.fn, r.fd = f, fd
      r.used = fl_top[i] + r.ht + fl_bot[i] + (p.colmode and f > 0 and (r.dp + f) or 0)
      res[i] = r
      if not ok then break end
    end
    if not ok then
      for _, r in pairs(res) do if r.list then flush_list(r.list) end end
      tex.setbox(SCR, nil)
      return nil
    end
    return res
  end

  local function free_res(res)
    for _, r in ipairs(res) do if r.list then flush_list(r.list) end end
  end
  local step = 65536

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
    for c = from, to do
      cur[j] = c
      enum(j + 1, c, cur, fixed)
    end
  end
  enum(1, 1, {}, false)
  if #assigns > 64 then
    assigns = {}
    enum(1, 1, {}, true)
  end
  local best, besth, bestmoves
  for _, a in ipairs(assigns) do
    set_assign(a)
    local hh = min_h()
    info('  placement %s: %s', table.concat(a, ','), hh and pt(hh) or 'does not fit')
    if hh then
      local moves = 0
      for j, f in ipairs(F) do
        if not f.deferred then moves = moves + a[j] - math.min(f.orig, N) end
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
      if p.colmode and r.fn > 0 then
        -- 段下端の脚注はfilで段の下端に付くので，本文（と下のフロート）の後に
        -- 脚注が収まる最初の行の位置（字面の下端）をこの段の下端とみなす
        -- 脚注の最終行のベースラインを，本文の後で脚注が収まる最初の行の位置に置く
        local B = fl_top[i] + (r.list and lastbase(r.list) or 0)
        local need = (r.list and r.dp or 0) + fl_bot[i] + r.fn
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
      elseif r.ht == 0 and (#tops[i] + #bots[i]) > 0 and not (p.colmode and r.fn > 0) then
        -- フロートだけの段：フロートの下端まで（後ろのアキは数えない）
        local t = 0
        for j, f in ipairs(tops[i]) do t = t + f.height + f.depth + (j > 1 and floatsep or 0) end
        for j, f in ipairs(bots[i]) do
          t = t + f.height + f.depth + ((j > 1 or #tops[i] > 0) and floatsep or 0)
        end
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
  if misaligned(res, nat, over) then
    local hh, hmax = h + step, colht
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
  h = bottom
  -- 揃えた段組の最終行のベースライン：本文で終わって下端に達した段があれば
  -- その最終行，なければ本文の行の深さだけ下端から上
  local base
  for i = 1, N do
    local endstext = res[i].list and not (#bots[i] > 0)
                     and not (p.colmode and res[i].fn > 0)
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
  info('balanced at %s (colht %s, text %s)', pt(h), pt(colht), pt(total_h))
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
  local usefnpage = false
  for i = 1, N do
    local r = res[i]
    local l = newlist()
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
      end
      append(l, figrule(p.topfig))
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
    -- 段の高さ：見かけの下端がそろう位置．版面下端の脚注があれば，組み上げた
    -- 脚注の並びの実際の高さの分だけ上で止める
    local target = h - over[i]
    local pushed = false
    if not p.colmode and fl.head then
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
    -- 本文の下のアキ：下フロートと（段下端モードの）脚注は段の下端に付ける
    if ragged or (p.colmode and #ids > 0) then
      append(l, filglue())
    end
    if #bots[i] > 0 then
      if ext_bot[i] > 0 then append(l, mkglue(ext_bot[i])) end
      append(l, regglue('textfloatsep'))
      append(l, figrule(p.botfig))
      for j, f in ipairs(bots[i]) do
        if j > 1 then append(l, regglue('floatsep')) end
        append(l, f)
      end
    end
    local body
    if p.colmode then
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
    if M.debug then
      -- 実際に置かれた見かけの下端（グルーが伸びて届いたか）
      local b = body
      if fl.head and not p.colmode then b = body.list end
      -- 段下端の脚注はfilで段の下端に付けてある
      local filfn = p.colmode and #ids > 0
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
      if ragged and not filfn then placed = nat[i] end
      local floatsonly = r.ht == 0 and (#tops[i] + #bots[i]) > 0
      -- 伸ばせるグルーがなくて届かない（行送りの位置にそろわない組版の限界）
      local nostretch = not ragged and not filfn and b.glue_sign ~= 1 and placed < target - 655
      info('  column %d placed %s%s', i, pt(placed + over[i]),
        pushed and ' (pushed)' or floatsonly and ' (floats only)'
        or colbreak and ' (column break)'
        or (blocked and (ragged or nostretch)) and ' (blocked)'
        or ragged and ' (ragged)' or nostretch and ' (no stretch)' or '')
    end
    local o = newlist()
    append(o, body)
    append(o, vssglue())
    M.out[i] = vpack(o.head, p.block and h or colht, 'exactly')
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
  -- 使われなかった脚注断片（本来は無いはず）を片付ける
  for _, id in ipairs(segorder) do
    if segs[id].head then flush_list(segs[id].head) end
  end
  flush_list(text.head)
  tex.setdimen('global', 'evenend@ruleht', usefnpage and colht or h)
  local colboxht = p.block and h or colht
  tex.setdimen('global', 'evenend@colboxht', colboxht)
  tex.setdimen('global', 'evenend@rowht', colboxht + dblh)
  -- 段抜きフロートで終わるときは，その下端から本文の行の深さだけ上を最終行とみなす
  if dblh > 0 then
    local d = 0
    for i = 1, N do if res[i].list and res[i].dp > d then d = res[i].dp end end
    base = colboxht + dblh - d
  end
  tex.setdimen('global', 'evenend@baseline', base)
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
  tex.setbox(n, b)
end

return M
