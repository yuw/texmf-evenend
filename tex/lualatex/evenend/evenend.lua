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

-- 垂直リストの最後の要素が，その基準線より下に見かけの上で出る分
-- （行なら深さ．垂直の箱なら，中身が箱の下端からはみ出す分も含める．中身を
-- グルーで下へずらして負のグルーで戻す箱もあるので，グルーで下った位置も見る）
local function overhang(head)
  if not head then return 0 end
  local t = node.tail(head)
  while t and t.id == WHATSIT do t = t.prev end
  if not t then return 0 end
  if t.id == HLIST then return t.depth end
  if t.id == VLIST then
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
  return 0
end

local function boxlist_copy(n)
  local b = n and tex.getbox(n)
  if b and b.list then return copy_list(b.list) end
  return nil
end

-- 末尾の除去可能な項目（グルー・カーン・ペナルティ）を取り除く
local function strip_tail(head, all)
  if not head then return nil end
  local t = node.tail(head)
  while t and is_discardable(t) do
    if not all and not (t.id == GLUE and t.stretch_order > 0)
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
  -- ここで写しをとっておく（強制改段のペナルティは除く）
  local d = newlist()
  local n = tex.lists.contrib_head
  while n and is_discardable(n) do
    if not (n.id == PENALTY and n.penalty <= -10000) then
      append(d, node.copy(n))
    end
    n = n.next
  end
  c.disc = d.head
  c.fn = boxlist_copy(footins)
  M.cols[#M.cols + 1] = c
  info('captured column %d', #M.cols)
end

function M.addfloat(where, boxnum)
  local c = M.cols[#M.cols]
  local b = tex.getbox(boxnum)
  if c and b then
    table.insert(c[where], node.copy(b))
  end
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
  if M.out then
    for _, b in pairs(M.out) do node.free(b) end
    M.out = nil
  end
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
function M.balance(p)
  local cols = M.cols
  local N, colht = p.N, p.colht
  tex.setcount('global', 'evenend@status', 0)
  if #cols == 0 then
    info('nothing captured')
    return
  end
  if #cols > N then
    info('captured %d columns for %d', #cols, N)
    return
  end

  -- 1. 本文を1本の垂直リストに繋ぎ直す
  local text = newlist()
  for k, c in ipairs(cols) do
    local t = c.text
    c.text = nil
    t = strip_tail(t, k == #cols)
    if k > 1 then
      t = strip_topskip(t)
      append(text, cols[k - 1].disc)
      cols[k - 1].disc = nil
    end
    append(text, t)
  end
  text.head = strip_tail(text.head, true)

  -- 2. 脚注を番号ごとの断片に分ける（段をまたいで分割されたものは繋ぐ）
  local fnattr = M.fnattr
  local segs, segorder = {}, {}
  for k, c in ipairs(cols) do
    local pending = newlist()
    local last
    local n = c.fn
    c.fn = nil
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
    if n == 0 then return 0 end
    return footskip + rule_h + sum - lastd
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
  local fl_top, fl_bot, fl_shrink = {}, {}, {}
  for i = 1, N do
    local c = cols[i]
    local t, b = 0, 0
    fl_shrink[i] = 0
    if c then
      local n = #c.top + #c.bot
      if n > 0 then
        fl_shrink[i] = (#c.top > 0 and tfs_sh or 0) + (#c.bot > 0 and tfs_sh or 0)
                       + (n - (#c.top > 0 and 1 or 0) - (#c.bot > 0 and 1 or 0)) * fs_sh
      end
      for j, f in ipairs(c.top) do
        t = t + f.height + f.depth + (j > 1 and floatsep or 0)
      end
      if #c.top > 0 then t = t + topfig_h + textfloatsep end
      for j, f in ipairs(c.bot) do
        b = b + f.height + f.depth + (j > 1 and floatsep or 0)
      end
      if #c.bot > 0 then b = b + botfig_h + textfloatsep end
    end
    fl_top[i], fl_bot[i] = t, b
  end

  local total_h = natural(text.head)
  local SCR = p.scratch

  -- 段の高さhで詰めてみる．入り切れば段ごとの結果を返す
  local function fill(h)
    tex.setbox(SCR, (vpack(copy_list(text.head))))
    local res = {}
    local ok = true
    for i = 1, N do
      local fl = fl_top[i] + fl_bot[i]
      local function cap(fids)
        local f = fnblock(fids)
        if p.colmode then
          return h - fl - f
        else
          return math.min(h, colht - f) - fl
        end
      end
      local r = {}
      if i < N then
        local t = cap(fnids(i, {}))
        local saved = boxlist_copy(SCR)
        for iter = 1, 10 do
          local chunk
          if t > 0 and saved then
            chunk = tex.splitbox(SCR, t, 'exactly')
          end
          local list = chunk and chunk.list
          if chunk then chunk.list = nil; node.free(chunk) end
          local ids = list and collect_ids(list, {}) or {}
          local nh, nd = natural(list)
          local c2 = cap(fnids(i, ids))
          if nh <= c2 or not list then
            r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
            break
          end
          flush_list(list)
          if iter == 10 or c2 >= t then
            ok = false
            break
          end
          -- 脚注が入り切らない：本文を減らしてやり直す
          t = c2
          tex.setbox(SCR, saved and vpack(copy_list(saved)) or nil)
        end
        if saved then flush_list(saved) end
        if not ok then break end
      else
        local rest = tex.getbox(SCR)
        local list = rest and rest.list
        if rest then rest.list = nil end
        tex.setbox(SCR, nil)
        local ids = list and collect_ids(list, {}) or {}
        local nh, nd = natural(list)
        r.list, r.ids, r.ht, r.dp = list, ids, nh, nd
        if nh > cap(fnids(i, ids)) then ok = false end
      end
      local f = fnblock(fnids(i, r.ids))
      r.fn = f
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

  -- 4. 入り切る最小の高さを探す
  local allfl = 0
  for i = 1, N do allfl = allfl + fl_top[i] + fl_bot[i] end
  local lo = math.floor((total_h + allfl) / N) - 2 * p.blskip
  if lo < 0 then lo = 0 end
  local step = 65536
  local h, res = lo, nil
  while h <= colht do
    res = fill(h)
    if res then break end
    h = h + step
  end
  if not res then
    res = fill(colht)
    h = colht
  end
  if not res then
    info('could not balance (material does not fit)')
    flush_list(text.head)
    for _, id in ipairs(segorder) do flush_list(segs[id].head) end
    return
  end

  -- 5. 段の下端をそろえる高さを決める
  -- 段ごとに，自然な高さnat（段の上端から最後の要素の基準線まで）と，その下に
  -- 見かけの上で出る分over（本文の最終行の深さや，箱の中身が下にはみ出す分）を
  -- 求め，見かけの下端nat + overを全段でそろえる．
  -- ・本文で終わる段：最終行の字面の下端がそろう
  -- ・下のフロートで終わる段：本文の最終行の深さも積まれるのでnatに数える
  -- ・段下端の脚注で終わる段：脚注の最終行の基準線までをnatとする
  local nat, over = {}, {}
  for i = 1, N do
    local r, c = res[i], cols[i]
    local hasbot = c and #c.bot > 0
    if p.colmode and r.fn > 0 then
      -- 脚注の最終行の深さ（fnblockは数えていない）
      local fids, d = fnids(i, r.ids), 0
      for _, id in ipairs(fids) do if segs[id] then d = segs[id].dp end end
      nat[i], over[i] = r.used, d
    elseif hasbot then
      nat[i], over[i] = fl_top[i] + r.ht + (r.list and r.dp or 0) + fl_bot[i], 0
    else
      nat[i], over[i] = fl_top[i] + r.ht, overhang(r.list)
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
  info('balanced at %s (colht %s, text %s)', pt(h), pt(colht), pt(total_h))
  for i = 1, N do
    local r, c = res[i], cols[i]
    info('  column %d: text %s+%s, floats %s (top %d, bottom %d), footnotes %s, bottom %s+%s',
      i, pt(r.ht), pt(r.dp), pt(fl_top[i] + fl_bot[i]), c and #c.top or 0,
      c and #c.bot or 0, pt(r.fn), pt(nat[i]), pt(over[i]))
  end

  -- 6. 段を組み立てる
  local function figrule(n)
    return boxlist_copy(n)
  end
  M.out = {}
  local usefnpage = false
  for i = 1, N do
    local r = res[i]
    local c = cols[i]
    local l = newlist()
    if c and #c.top > 0 then
      for j, f in ipairs(c.top) do
        if j > 1 then append(l, regglue('floatsep')) end
        append(l, f)
      end
      c.top = {}
      append(l, figrule(p.topfig))
      append(l, regglue('textfloatsep'))
    end
    append(l, r.list)
    r.list = nil
    local ids = fnids(i, r.ids)
    -- 段の高さ：見かけの下端がそろう位置
    local target = h - over[i]
    if not p.colmode and #ids > 0 then target = math.min(target, colht - r.fn) end
    -- 段の高さに届かない段（行の足りない最終段や，版面下端の脚注に押された段）は
    -- グルーを伸ばさずに下を空ける
    local ragged = target - nat[i] > p.blskip / 2
    -- 本文の下のアキ：下フロートと（段下端モードの）脚注は段の下端に付ける
    if ragged or (p.colmode and #ids > 0) then
      append(l, filglue())
    end
    if c and #c.bot > 0 then
      append(l, regglue('textfloatsep'))
      append(l, figrule(p.botfig))
      for j, f in ipairs(c.bot) do
        if j > 1 then append(l, regglue('floatsep')) end
        append(l, f)
      end
      c.bot = {}
    end
    local fl = newlist()
    if #ids > 0 then
      append(fl, regglue(p.footins))
      append(fl, boxlist_copy(p.fnrule))
      for _, id in ipairs(ids) do
        append(fl, segs[id].head)
        segs[id].head = nil
      end
    end
    local body
    if p.colmode then
      append(l, fl.head)
      body = vpack(l.head, target, 'exactly')
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
    local o = newlist()
    append(o, body)
    append(o, vssglue())
    M.out[i] = vpack(o.head, colht, 'exactly')
  end
  -- 使われなかった脚注断片（本来は無いはず）を片付ける
  for _, id in ipairs(segorder) do
    if segs[id].head then flush_list(segs[id].head) end
  end
  flush_list(text.head)
  tex.setdimen('global', 'evenend@ruleht', usefnpage and colht or h)
  tex.setdimen('global', 'evenend@height', h)
  tex.setcount('global', 'evenend@status', 1)
end

-- 組み上がったi段目を箱レジスタnに入れる
function M.getcolumn(i, n)
  local b = M.out and M.out[i]
  if b then M.out[i] = nil end
  tex.setbox(n, b)
end

return M
