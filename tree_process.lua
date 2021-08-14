#!/bin/sh
_=[[
exec lua "$0" "$@"

#! lua

]]

local freshnames, arguments, referent, fact = {}, {}, 0, 0

function concat(div, expr1, expr2)
  local out
  if expr1 == "" then
    out = expr2
  elseif expr2 == "" then
    out = expr1
  else
    out = string.format("%s%s%s", expr1, div, expr2)
  end
  return out
end

function get_sort(str,default)
  if type(str) == 'string' then
    str = string.gsub(str, "^.*(%b{}).*$", "%1")
    if string.find(str, '^{') and string.find(str, '}$') then
      str = string.sub(str, 2, #str-1)
      str = string.gsub(str, "+", "pLus")
    else
      str = default
    end
  else
    str = default
  end
  return str
end

function clean_id(str)
  str = string.gsub(str, "%-", "dAsh")
  return str
end

function make_list(tbl, items)
  for k in pairs(tbl) do
    if not(string.find(k, "^'%*") and string.find(k, "%*'$")) then
      items = concat(",", items, k)
    end
  end
  return string.format("[%s]", items)
end

function find_control_candidates(tbl)
  local controllers = {}
  if type(tbl) == 'table' then
    for k in pairs(tbl) do
      if k == "'h'" then
        controllers["h"] = 1
      elseif string.find(k, "arg0") then
        controllers["arg0"] = 1
      elseif string.find(k, "arg1") then
        controllers["arg1"] = 1
      elseif string.find(k, "arg2") then
        controllers["arg2"] = 1
      end
    end
  end
  return controllers
end

function copy_list(tbl)
  local out = {}
  for k, v in pairs(tbl) do
    out[k] = v
  end
  return out
end

function make_ordered_list(tbl)
  local items = ""
  for i=1,#tbl do
    items = concat(",", items, tbl[i])
  end
  return string.format("[%s]", items)
end

function make_link(lab, s, i)
  if string.find(lab, '^%*') and string.find(lab, '%*$') then
    return lab
  else
    return make_link_full(lab, s, i)
  end
end

function make_link_full(lab, s, i)
  local str = ""
  -- links by type
  if string.find(lab, '^ADJP') then
    str = concat("_", str, "attribute")
  end
  if string.find(lab, '^ADVP') then
    str = concat("_", str, "modifier")
  end
  if string.find(lab, '%-SCON') then
    str = concat("_", str, "scon")
  end
  if string.find(lab, '%-CND') then
    str = concat("_", str, "cnd")
  end
  -- selected argument links
  if string.find(lab, 'SBJ') then
    str = "arg0"
  elseif string.find(lab, '%-DOB1') then
    str = "darg1"
  elseif string.find(lab, 'OB1') then
    str = "arg1"
  elseif string.find(lab, 'OB2') then
    str = "arg2"
  elseif string.find(lab, '%-PRD2') then
    str = "prd2"
  elseif string.find(lab, '%-PRD') then
    str = "prd"
  elseif string.find(lab, '%-LGS') then
    str = "lgs"
  elseif string.find(lab, '%-GENV') then
    str = "genv"
  elseif string.find(lab, '%-VOC') then
    str = "voc"
  elseif string.find(lab, '%-FOC') then
    str = "foc"
  elseif string.find(lab, '%-CLF') then
    str = "clf"
  end
  -- adverbial links
  if string.find(lab, '%-ABS') then
    str = concat("_", str, "abs")
  elseif string.find(lab, '%-BNF') then
    str = concat("_", str, "bnf")
  elseif string.find(lab, '%-CNT') then
    str = concat("_", str, "cnt")
  elseif string.find(lab, '%-COM') then
    str = concat("_", str, "com")
  elseif string.find(lab, '%-DIR') then
    str = concat("_", str, "dir")
  elseif string.find(lab, '%-LOC') then
    str = concat("_", str, "loc")
  elseif string.find(lab, '%-MNR') then
    str = concat("_", str, "mnr")
  elseif string.find(lab, '%-MOD') then
    str = concat("_", str, "mod")
  elseif string.find(lab, '%-OBU') then
    str = concat("_", str, "obu")
  elseif string.find(lab, '%-RST') then
    str = concat("_", str, "rst")
  elseif string.find(lab, '%-TMP') then
    str = concat("_", str, "tmp")
  end
  -- return result
  if str == 'arg0' or str == 'arg1' or str == 'darg1' or str == 'arg2' or str == 'lgs'
      or str == 'prd2' or str == 'prd' or str == 'genv' or str == 'foc' then
    return string.format("'%s'", concat("_", str, s))
  elseif str == '' and s == '' then
    return string.format("'link%s'", i)
  elseif s == '' then
    return string.format("'%s%s'", str, i)
  else
    return string.format("'%s'", concat("_", str, s))
  end
end

function make_connrole_headword(expr)
  -- default headword is a predicate with the empty string
  local headword = ""
  -- add to the headword string
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      tag = string.gsub(tag, "^%f[%w]P%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]CONJ%f[%W].*", "headword")
      if tag == "headword" then
        headword = concat("_", headword, expr[i][2])
      end
    end
  end
  -- construct and return the headword as a predicate
  return headword
end

function dummy_np(link, mainpart)
  local fresh = "'@e'"
  freshnames[fresh] = 1
  return string.format("namely(c('DUMMY',''), %s, mov(%s, %s, %s))", fresh, fresh, link, mainpart)
end

function process_np(expr, link, mainpart)
  local sort = get_sort(expr[1],'')
  if expr[2] == '*' then
    return dummy_np(link, mainpart)
  elseif expr[2][1] == 'RPRO' then
    return string.format("mov('T', %s, %s)", link, mainpart)
  elseif expr[2] == '*T*' then
    return string.format("mov('T', %s, %s)", link, mainpart)
  elseif type(expr[2]) == 'string' and string.find(expr[2], "^%*") and string.find(expr[2], "%*$") then
    return string.format("mov('%s', %s, %s)", expr[2], link, mainpart)
  elseif sort == 'DUMMY' then
    return dummy_np(link, mainpart)
  elseif string.find(expr[1], '^NP%-CSBJ') then
    return dummy_np(link, mainpart)
  elseif string.find(expr[1], '^NP%-PSBJ') then
    return dummy_np(link, mainpart)
  elseif sort == '' then
    -- no sort, so change any pro to npr
    return process_np_full(sort, change_pro_to_npr(expr), link, mainpart)
  else
    return process_np_full(sort, expr, link, mainpart)
  end
end

function change_pro_to_npr(expr)
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      if string.sub(expr[i][1],1,3) == 'PRO' then
        expr[i][1] = 'NPR'
      elseif string.sub(expr[i][1],1,3) == 'PNX' then
        expr[i][1] = 'NPR'
      end
    end
  end
  return expr
end

function process_np_full(sort, expr, link, mainpart)
  -- default sort for binding
  if sort == '' then
    sort = "ENTITY"
  end
  -- establish local arguments
  local arguments = {}
  arguments["'h'"] = 1
  -- establish available bindings for np
  local available = {}
  -- establish local binding names for restriction
  local localnames = {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      if string.find(tag, '^ADJP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^ADVP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^RD') then
        localnames[i] = string.format("'equals%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^Q') then
        localnames[i] = string.format("'quant%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^NEG') then
        localnames[i] = string.format("'neg%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^NUM') then
        localnames[i] = string.format("'num%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^NP%-') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][2][1], '^NP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^multi%-sentence') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-PPL') then
        available[i] = copy_list(arguments)
      elseif string.find(tag, '^CP%-THT') then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^CP%-QUE') then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-INF') and not(string.find(tag, '^IP%-INF%-REL')) then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^FRAG') then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^FRAG') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADVP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      end
    end
  end
  -- create restriction kernel
  local body, headword = process_np_head(expr, arguments)
  local constant = ''
  if string.find(body, "^pred%('xxx%d+', %['h'%]%)$") then
    constant = process_np_constant(expr)
  elseif string.find(process_np_constant(expr), headword) and body == string.format("pred('%s', ['h'])", headword) then
    constant = process_np_constant(expr)
    fact = fact + 1
    body = string.format("pred('xxx%s', ['h'])", fact)
  end
  -- construct rest of the restriction
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      if string.find(tag, '^ADJP') then
        body = process_adxp(expr[i], localnames[i], body)
      elseif string.find(tag, '^ADVP') then
        body = process_adxp(expr[i], localnames[i], body)
      elseif string.find(tag, '^RD') then
        body = string.format("mov('T', %s, %s)", localnames[i], body)
      elseif string.find(tag, '^Q') then
        local fresh = "'@e'"
        freshnames[fresh] = 1
        body = string.format("someClassic(%s, c('Q','%s'), %s, %s)", fresh, expr[i][2], localnames[i], body)
      elseif string.find(tag, '^NEG') then
        local fresh = "'@e'"
        freshnames[fresh] = 1
        body = string.format("someClassic(%s, c('NEG','%s'), %s, %s)", fresh, expr[i][2], localnames[i], body)
      elseif string.find(tag, '^NUM') then
        local fresh = "'@e'"
        freshnames[fresh] = 1
        body = string.format("someClassic(%s, c('NUM','%s'), %s, %s)", fresh, expr[i][2], localnames[i], body)
      elseif string.find(tag, '^NP%-') then
        body = process_np(expr[i], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        body = process_np(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][2][1], '^NP') then
        body = process_np(expr[i][2], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^multi%-sentence') then
        body = process_multi_sentence_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-PPL') then
        body = process_ip_control_connect(expr[i], body, available[i], "'&'", "")
      elseif string.find(tag, '^IP%-REL') then
        body = process_ip_rel_connect(expr[i], body)
      elseif string.find(tag, '^IP%-INF%-REL') then
        body = process_ip_rel_connect(expr[i], body)
      elseif string.find(tag, '^CP%-THT') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^CP%-QUE') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-INF') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^FRAG') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        body = process_np(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^FRAG') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADVP') then
        body = process_adxp(expr[i][#expr[i]], localnames[i], body)
      end
    end
  end
  local fresh, dref
  if constant == '' then
    -- bound discourse referent
    fresh = "'.e'"
    referent = referent + 1
    -- create discourse referent
    dref = string.format("x('%s', %s)", sort, referent)
  else
    -- constant discourse referent
    fresh = "'@e'"
    -- create discourse referent
    dref = string.format("c('%s', '%s')", sort, constant)
  end
  freshnames[fresh] = 1
  if string.find(body, "^pred%('xxx%d+', %['h'%]%)$") and constant == "" then
    local determiner = process_np_det(expr)
    mainpart = process_pronominal(fresh, expr, link, mainpart, sort, determiner)
    -- no restriction
    if string.find(mainpart, '^pick') then
      return string.format("someClassic(%s, %s, %s, %s)", fresh, dref, link, mainpart)
    elseif not(determiner == "") then
      return string.format("someClassic_rest(%s, %s, local(%s, pred('%s', ['h'])), %s, %s)", fresh, dref, make_list(arguments, ""), determiner, link, mainpart)
    else
      return string.format("namely(%s, %s, mov(%s, %s, %s))", dref, fresh, fresh, link, mainpart)
    end
  else
    mainpart = process_pronominal(fresh, expr, link, mainpart, sort, "")
    -- with restriction
    if string.find(mainpart, '^pick') then
      return string.format("someClassic_rest(%s, %s, local(%s, %s), %s, %s)", fresh, dref, make_list(arguments, ""), body, link, mainpart)
    elseif string.find(body, "^pred%('xxx%d+', %['h'%]%)$") then
      return string.format("namely(%s, %s, mov(%s, %s, %s))", dref, fresh, fresh, link, mainpart)
    else
      return string.format("some(%s, %s, local(%s, %s), %s, %s)", fresh, dref, make_list(arguments, ""), body, link, mainpart)
    end
  end
end

function process_np_head(expr, arguments)
  -- collect information about any conjuncts
  local conn, conjn, conj_links = "", 0, {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^NML') then
      for j=2,#expr[i] do
        if type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conn = concat("_", conn, make_connrole_headword(expr[i][j]))
        elseif type(expr[i][j][1]) == 'string' and type(expr[i][j][2]) == 'string' and string.find(expr[i][j][1], '^CONJ') then
          conn = concat("_", conn, expr[i][j][2])
        elseif type(expr[i][j][1]) == 'string' and type(expr[i][j][2]) == 'string' and string.find(expr[i][j][1], '^NEG') then
          conn = concat("_", conn, expr[i][j][2])
        end
      end
    end
  end
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and  type(expr[i][1]) == 'string' and string.find(expr[i][1], '^NML') then
      for j=2,#expr[i] do
        if type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^NP') and not(string.find(expr[i][j][1], '^NP%-')) then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^NP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^IP') and not(string.find(expr[i][j][1], '^IP%-REL')) and not(string.find(expr[i][j][1], '^IP%-PPL')) then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^IP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        end
      end
      if conjn == 0 then
        arguments[string.format("'nml%s'", i-1)] = 1
      end
    end
  end
  -- default restriction is a predicate with the empty string
  local body, headword = "", ""
  -- add to the headword string
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      tag = string.gsub(tag, "^%f[%w]NPR%f[%W].*", "proper")
      tag = string.gsub(tag, "^%f[%w]NPRS%f[%W].*", "proper")
      tag = string.gsub(tag, "^%f[%w]WPRO%f[%W].*", "noun")
      tag = string.gsub(tag, "^%f[%w]WD%f[%W].*", "noun")
      tag = string.gsub(tag, "^%f[%w]N%f[%W].*", "noun")
      tag = string.gsub(tag, "^%f[%w]NS%f[%W].*", "noun")
      tag = string.gsub(tag, "^%f[%w]FO%f[%W].*", "noun")
      if tag == "noun" then
        headword = concat("_", expr[i][2], headword)
      elseif tag == "proper" and #headword > 0 then
        headword = concat("_", expr[i][2], headword)
      end
    end
  end
  -- add any conn information to headword string
  if #conn > 0 then
    headword = concat("_", conn, headword)
  end
  -- construct the restriction
  local listargs = make_list(arguments, "")
  if headword == '' and not(listargs == "['h']") then
    headword = process_np_constant(expr)
  end
  if headword == '' then
    fact = fact + 1
    headword = string.format("xxx%s", fact)
  end
  body = string.format("pred('%s', %s)", headword, listargs)
  -- add conjuncts
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^NML') then
      for j = #expr[i], 2, -1 do
        if type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^NP') and not(string.find(expr[i][j][1], '^NP%-')) then
          body = process_np(expr[i][j], string.format("'conj%s'", conj_links[j]), body)
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^NP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          body = process_np(expr[i][j][#expr[i][j]], string.format("'conj%s'", conj_links[j]), body)
        elseif type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^IP') and not(string.find(expr[i][j][1], '^IP%-REL')) and not(string.find(expr[i][j][1], '^IP%-PPL')) then
          body = process_ip_embed_fact(expr[i][j], string.format("'conj%s'", conj_links[j]), body, "FACT")
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^IP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          body = process_ip_embed_fact(expr[i][j][#expr[i][j]], string.format("'conj%s'", conj_links[j]), body, "FACT")
        end
      end
      if conjn == 0 then
        body = process_np(expr[i], string.format("'nml%s'", i-1), body)
      end
    end
  end
  -- construct and return the restriction as a predicate
  return body, headword
end

function process_pronominal(fresh, expr, link, mainpart, sort, determiner)
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      if string.find(expr[i][1], '^PRO') then
        mainpart = string.format("pick(%s, ['%s'], '%s', %s, %s)", fresh, sort, 'equals__' .. expr[i][2], link, mainpart)
      elseif string.find(expr[i][1], '^PNX') then
        mainpart = string.format("pick_more(%s, ['%s'], '%s', %s, %s)", fresh, sort, 'equals__' .. expr[i][2], link, mainpart)
      elseif string.find(determiner, '^th') and not(sort == "ENTITY") then
        mainpart = string.format("pick(%s, ['%s'], '%s', %s, %s)", fresh, sort, 'equals__' .. determiner, link, mainpart)
      end
    end
  end
  return mainpart
end

function process_np_det(expr)
  local headword = ""
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      tag = string.gsub(tag, "^%f[%w]D%f[%W].*", "det")
      if tag == "det" then
        headword = concat("_", expr[i][2], headword)
      end
    end
  end
  return headword
end

function process_np_constant(expr)
  local headword = ""
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      tag = string.gsub(tag, "^%f[%w]N%f[%W].*", "noun")
      tag = string.gsub(tag, "^%f[%w]NS%f[%W].*", "noun")
      tag = string.gsub(tag, "^%f[%w]NPR%f[%W].*", "proper")
      tag = string.gsub(tag, "^%f[%w]NPRS%f[%W].*", "proper")
      if tag == "proper" then
        headword = concat("_", expr[i][2], headword)
      elseif tag == "noun" and #headword > 0 then
        headword = concat("_", expr[i][2], headword)
      end
    end
  end
  return headword
end

function process_adxp(expr, link, mainpart)
  if expr[2][1] == 'RADV' then
    return string.format("mov('T', %s, %s)", link, mainpart)
  else
    return process_adxp_full(expr, link, mainpart)
  end
end

function process_adxp_full(expr, link, mainpart)
  -- establish sort for binding
  local sort = get_sort(expr[1],"ATTRIB")
  -- establish local arguments
  local arguments = {}
  arguments["'h'"] = 1
  -- establish available bindings for adxp
  local available = {}
  -- establish local binding names for restriction
  local localnames = {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      if string.find(tag, '^ADJP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^ADVP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^NP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^CP%-THT') then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^CP%-QUE') then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-INF') then
        localnames[i] = string.format("'emb%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^FRAG') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      end
    end
  end
  -- create restriction
  local body = process_adxp_head(expr, arguments)
  -- construct restriction
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      if string.find(tag, '^ADJP') then
        body = process_adxp(expr[i], localnames[i], body)
      elseif string.find(tag, '^ADVP') then
        body = process_adxp(expr[i], localnames[i], body)
      elseif string.find(tag, '^NP') then
        body = process_np(expr[i], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        body = process_np(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^CP%-THT') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^CP%-QUE') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-INF') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        body = process_np(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^FRAG') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      end
    end
  end
  -- establish fresh source for binding
  local fresh = "'.attrib'"
  freshnames[fresh] = 1
  -- increment referent for fresh value
  referent = referent + 1
  -- create discourse referent
  local dref = string.format("x('%s', %s)", sort, referent)
  -- construct ADXP
  return string.format("someClassic_rest(%s, %s, local(%s, %s), %s, %s)", fresh, dref, make_list(arguments, ""), body, link, mainpart)
end

function process_adxp_head(expr, arguments)
  -- collect information about any conjuncts
  local conn, conjn, conj_links = "", 0, {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^AML') then
      for j=2,#expr[i] do
        if type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conn = concat("_", conn, make_connrole_headword(expr[i][j]))
        elseif type(expr[i][j][1]) == 'string' and type(expr[i][j][2]) == 'string' and string.find(expr[i][j][1], '^CONJ') then
          conn = concat("_", conn, expr[i][j][2])
        elseif type(expr[i][j][1]) == 'string' and type(expr[i][j][2]) == 'string' and string.find(expr[i][j][1], '^NEG') then
          conn = concat("_", conn, expr[i][j][2])
        end
      end
    end
  end
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^AML') then
      for j=2,#expr[i] do
        if type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^ADJP') and not(string.find(expr[i][j][1], '^ADJP%-')) then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^ADVP') and not(string.find(expr[i][j][1], '^ADVP%-')) then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^ADJP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^ADVP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s'", conjn)] = 1
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^PP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          conjn = conjn + 1
          conj_links[j] = conjn
          arguments[string.format("'conj%s_%s'", conjn, make_connrole_headword(expr[i][j][#expr[i][j]]))] = 1
        end
      end
      if conjn == 0 then
        arguments[string.format("'aml%s'", i-1)] = 1
      end
    end
  end
  -- default restriction is a predicate with the empty string
  local body, headword = "", ""
  -- add to the headword string
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      -- headword is an adjective
      tag = string.gsub(tag, "^%f[%w]ADJ%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]ADJR%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]ADJS%f[%W].*", "headword")
      -- headword is an adverb
      tag = string.gsub(tag, "^%f[%w]WADV%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]ADV%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]ADVR%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]ADVS%f[%W].*", "headword")
      -- headword is from another word class
      tag = string.gsub(tag, "^%f[%w]CONJ%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]NUM%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]P%-ROLE%f[%W].*", "headword")
      tag = string.gsub(tag, "^%f[%w]RP%f[%W].*", "headword")
      if tag == "headword" then
        headword = concat("_", headword, expr[i][2])
      end
    end
  end
  -- add any conn information to headword string
  if #conn > 0 then
    headword = concat("_", conn, headword)
  end
  -- construct the restriction
  if headword == '' then
    fact = fact + 1
    headword = string.format("xxx%s", fact)
  end
  body = string.format("pred('%s', %s)", headword, make_list(arguments, ""))
  -- add conjuncts
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^AML') then
      for j = #expr[i], 2, -1 do
        if type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^ADJP') and not(string.find(expr[i][j][1], '^ADJP%-')) then
          body = process_adxp(expr[i][j], string.format("'conj%s'", conj_links[j]), body)
        elseif type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^ADVP') and not(string.find(expr[i][j][1], '^ADVP%-')) then
          body = process_adxp(expr[i][j], string.format("'conj%s'", conj_links[j]), body)
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^ADJP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          body = process_adxp(expr[i][j][#expr[i][j]], string.format("'conj%s'", conj_links[j]), body)
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^ADVP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          body = process_adxp(expr[i][j][#expr[i][j]], string.format("'conj%s'", conj_links[j]), body)
        elseif type(expr[i][j][#expr[i][j]][1]) == 'string' and string.find(expr[i][j][#expr[i][j]][1], '^PP') and type(expr[i][j][1]) == 'string' and string.find(expr[i][j][1], '^CONJP') then
          body = process_np(expr[i][j][#expr[i][j]][#expr[i][j][#expr[i][j]]], string.format("'conj%s_%s'", conj_links[i], make_connrole_headword(expr[i][j][#expr[i][j]])), body)
        end
      end
      if conjn == 0 then
        body = process_adxp(expr[i], string.format("'aml%s'", i-1), body)
      end
    end
  end
  -- construct and return the restriction as a predicate
  return body
end

function process_clause(expr, arguments, clausetype)
  if type(expr[1]) == 'string' and string.find(expr[1], '^CP%-QUE') then
    return process_clause_full(expr[2], arguments, "question")
  elseif type(expr[1]) == 'string' and string.find(expr[1], '^CP%-') then
    return process_clause_full(expr[2], arguments, clausetype)
  else
    return process_clause_full(expr, arguments, clausetype)
  end
end

function process_clause_full(expr, arguments, clausetype)
  -- reset local arguments
  if type(expr[1]) == 'string' and string.find(expr[1], '^IP%-MAT') then
    arguments = {}
  end
  -- establish clause type argument
  if clausetype == "question" then
    arguments["'clausetype'"] = 1
  elseif type(expr[1]) == 'string' and string.find(expr[1], '%-QUE') then
    arguments["'clausetype'"] = 1
  elseif type(expr[1]) == 'string' and string.find(expr[1], '%-IMP') then
    arguments["'clausetype'"] = 1
  end
  -- establish sort for entity binding
  local sort = get_sort(expr[1],"EVENT")
  -- establish available bindings for clause
  local available = {}
  -- establish local binding names for clause
  local localnames = {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      if string.find(tag, '^IP%-PPL%-SEQ') then
        localnames[i] = "'seq'"
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-PPL%-CAT') then
        localnames[i] = "'cat'"
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^MD') then
        localnames[i] = string.format("'md%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^NEG') then
        localnames[i] = string.format("'neg%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^ADJP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^ADVP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^CP%-THT') then
        localnames[i] = make_link(tag, "", i-1)
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^CP%-QUE%-') then
        localnames[i] = make_link(tag, "", i-1)
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^CP%-QUE') then
        localnames[i] = string.format("'disc%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-INF%-CAT') then
        localnames[i] = "'cat'"
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-INF') then
        localnames[i] = make_link(tag, "", i-1)
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-PPL') then
        localnames[i] = make_link(tag, "", i-1)
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-ADV') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^FRAG%-') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^FRAG') then
        localnames[i] = string.format("'disc%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-MAT%-IMP%-') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-MAT%-IMP') then
        localnames[i] = string.format("'disc%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-MAT%-') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-MAT') then
        localnames[i] = string.format("'disc%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^multi%-sentence') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-CAR') then
        localnames[i] = string.format("'car%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^IP%-CLF') then
        localnames[i] = "clf"
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CONJP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP%-SCON') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), "")
        available[i] = copy_list(arguments)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADJP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADVP') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        available[i] = copy_list(arguments)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^multi%-sentence') then
        localnames[i] = make_link(tag, make_connrole_headword(expr[i]), i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^FRAG') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADVP') then
        localnames[i] = string.format("'prn%s'", i-1)
        arguments[localnames[i]] = 1
      elseif string.find(tag, '^NP') then
        localnames[i] = make_link(tag, "", i-1)
        arguments[localnames[i]] = 1
      end
    end
  end
  -- create body
  local body = process_clause_kernel(expr, sort, arguments)
  -- construct clause
  for i = #expr, 2, -1 do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      local tag = expr[i][1]
      if string.find(tag, '^IP%-PPL%-SEQ') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "2", "SEQ")
      elseif string.find(tag, '^IP%-PPL%-CAT') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "2", "CAT")
      elseif string.find(tag, '^MD') then
        local fresh = "'@e'"
        freshnames[fresh] = 1
        body = string.format("someClassic(%s, c('MODAL','%s'), %s, %s)", fresh, expr[i][2], localnames[i], body)
      elseif string.find(tag, '^NEG') then
        local fresh = "'@e'"
        freshnames[fresh] = 1
        body = string.format("someClassic(%s, c('NEG','%s'), %s, %s)", fresh, expr[i][2], localnames[i], body)
      elseif string.find(tag, '^ADJP') then
        body = process_adxp(expr[i], localnames[i], body)
      elseif string.find(tag, '^ADVP') then
        body = process_adxp(expr[i], localnames[i], body)
      elseif string.find(tag, '^CP%-THT') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-INF') then
        body = process_ip_control_fact(expr[i][2], localnames[i], body, available[i], "", "FACT")
      elseif string.find(tag, '^CP%-THT') then
        body = process_ip_embed_fact(expr[i][2], localnames[i], body, "FACT")
      elseif string.find(tag, '^CP%-QUE') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-INF') then
        body = process_ip_control_fact(expr[i][2], localnames[i], body, available[i], "", "FACT", "question")
      elseif string.find(tag, '^CP%-QUE') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-INF%-CAT') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "2", "CAT")
      elseif string.find(tag, '^IP%-INF3') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-INF2') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "2", "FACT")
      elseif string.find(tag, '^IP%-INF') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "", "FACT")
      elseif string.find(tag, '^IP%-PPL3') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-PPL2') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "2", "FACT")
      elseif string.find(tag, '^IP%-PPL') then
        body = process_ip_control_fact(expr[i], localnames[i], body, available[i], "", "FACT")
      elseif string.find(tag, '^IP%-ADV') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^FRAG') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-MAT') then
        body = process_ip_embed_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^multi%-sentence') then
        body = process_multi_sentence_fact(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-CAR') then
        body = process_ip_car(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^IP%-CLF') then
        body = process_ip_car(expr[i], localnames[i], body, "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CONJP') then
        body = process_pp_conj(expr[i], localnames[i], body)
      elseif string.find(tag, '^PP%-SCON') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL3') then
        body = process_ip_embed_connect(expr[i][#expr[i]], body, localnames[i])
      elseif string.find(tag, '^PP%-SCON') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL2') then
        body = process_ip_control_connect(expr[i][#expr[i]], body, available[i], localnames[i], "2")
      elseif string.find(tag, '^PP%-SCON') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL') then
        body = process_ip_control_connect(expr[i][#expr[i]], body, available[i], localnames[i], "")
      elseif string.find(tag, '^PP%-SCON') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-ADV') then
        body = process_ip_embed_connect(expr[i][#expr[i]], body, localnames[i])
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        body = process_np(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADJP') then
        body = process_adxp(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADVP') then
        body = process_adxp(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL3') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL2') then
        body = process_ip_control_fact(expr[i][#expr[i]], localnames[i], body, available[i], "2", "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP%-PPL') then
        body = process_ip_control_fact(expr[i][#expr[i]], localnames[i], body, available[i], "", "FACT")
      elseif string.find(tag, '^PP') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^multi%-sentence') then
        body = process_multi_sentence_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
        body = process_np(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^CP') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^FRAG') then
        body = process_ip_embed_fact(expr[i][#expr[i]], localnames[i], body, "FACT")
      elseif string.find(tag, '^PRN') and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^ADVP') then
        body = process_adxp(expr[i][#expr[i]], localnames[i], body)
      elseif string.find(tag, '^NP') then
        body = process_np(expr[i], localnames[i], body)
      end
    end
  end
  -- establish clause type
  if clausetype == "question" or (type(expr[1]) == 'string' and string.find(expr[1], '%-QUE')) then
    local fresh = "'@e'"
    freshnames[fresh] = 1
    fact = fact + 1
    body = string.format("someClassic(%s, c('CLAUSETYPE','question%s'), 'clausetype', %s)", fresh, fact, body)
  elseif type(expr[1]) == 'string' and string.find(expr[1], '%-IMP') then
    local fresh = "'@e'"
    freshnames[fresh] = 1
    fact = fact + 1
    body = string.format("someClassic(%s, c('CLAUSETYPE','imp%s'), 'clausetype', %s)", fresh, fact, body)
  end
  -- establish local binding names
  local local_args = make_list(arguments, "")
  if local_args == "[]" then
    return body
  else
    return string.format("local(%s, %s)", local_args, body)
  end
end

function process_clause_kernel(expr, sort, arguments)
  local kernel = ""
  -- take kernel from IML if present
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
      if string.find(expr[i][1], '^IML') then
         kernel = process_clause_iml(expr[i], arguments)
      end
    end
  end
  if kernel == "" then
    -- nothing from IML, so build a new kernel
    local headword = ""
    -- add to the headword string
    for i=2,#expr do
      if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' then
        local tag = expr[i][1]
        -- headword includes EX
        tag = string.gsub(tag, "^%f[%w]EX%f[%W].*", "headword")
        -- headword includes TO
        tag = string.gsub(tag, "^%f[%w]TO%f[%W].*", "headword")
        -- headword is HAVE
        tag = string.gsub(tag, "^%f[%w]HVP%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]HVD%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]HV%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]HAG%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]HVN%f[%W].*", "headword")
        -- headword is BE
        tag = string.gsub(tag, "^%f[%w]BEP%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]BED%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]BE%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]BAG%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]BEN%f[%W].*", "headword")
        -- headword is DO
        tag = string.gsub(tag, "^%f[%w]DOP%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]DOD%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]DO%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]DAG%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]DON%f[%W].*", "headword")
        -- headword is a full verb
        tag = string.gsub(tag, "^%f[%w]VBP%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]VBD%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]VB%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]VAG%f[%W].*", "headword")
        tag = string.gsub(tag, "^%f[%w]VVN%f[%W].*", "headword")
        -- headword is a particle
        tag = string.gsub(tag, "^%f[%w]RP%f[%W].*", "headword")
        if tag == "headword" then
          headword = concat("_", headword, expr[i][2])
        end
      end
    end
    if headword == '' then
      -- when there is no headword and the clause is a fragment
      if type(expr[1]) == 'string' and string.find(expr[1], '^FRAG') then
       fact = fact + 1
       headword = string.format("frag%s", fact)
      -- when there is still no headword, pick a default
      else
       fact = fact + 1
       headword = string.format("xxx%s", fact)
      end
    end
    -- establish fresh source for event binding
    local fresh = "'.event'"
    freshnames[fresh] = 1
    -- increment referent for fresh value
    referent = referent + 1
    -- create discourse referent
    local dref = string.format("x('%s', %s)", sort, referent)
    -- construct and return the kernel as a verb predicate
    kernel = string.format("namely(%s, %s, pred('%s', %s))", dref, fresh, headword, make_list(arguments, fresh))
  end
  return kernel
end

function process_ip_rel_connect(expr, mainpart)
  local arguments = {}
  if string.find(mainpart, "^pred%('xxx%d+', %['h'%]%)$") then
    return string.format("mov('h' ,'T', embed(%s))", process_clause(expr, arguments))
  else
    return string.format("connect('&', [%s, mov('h' ,'T', embed(%s))])", mainpart, process_clause(expr, arguments))
  end
end

function process_ip_control_connect(expr, mainpart, inherited, connect, version)
  local control_candidates = find_control_candidates(inherited)
  local arguments = {}
  if string.find(mainpart, "^pred%('xxx%d+', %['h'%]%)$") then
    -- preserve subject if present in higher clause layer
    if version == "2" and control_candidates["arg0"] then
      arguments["'arg0'"] = 1
      return string.format("control2(%s)", process_clause(expr, arguments))
    elseif control_candidates["arg0"] or control_candidates["arg1"] or control_candidates["arg2"] or control_candidates["h"] then
      arguments["'arg0'"] = 1
      return string.format("control(%s)", process_clause(expr, arguments))
    else
      return string.format("embed(%s)", process_clause(expr, arguments))
    end
  else
    -- preserve subject if present in higher clause layer
    if version == "2" and control_candidates["arg0"] then
      arguments["'arg0'"] = 1
      return string.format("connect(%s, [control2(%s), %s])", connect, process_clause(expr, arguments), mainpart)
    elseif control_candidates["arg0"] or control_candidates["arg1"] or control_candidates["arg2"] or control_candidates["h"] then
      arguments["'arg0'"] = 1
      return string.format("connect(%s, [control(%s), %s])", connect, process_clause(expr, arguments), mainpart)
    else
      return string.format("connect(%s, [embed(%s), %s])", connect, process_clause(expr, arguments), mainpart)
    end
  end
end

function process_ip_embed_connect(expr, mainpart, connect)
  local arguments = {}
  return string.format("connect(%s, [embed(%s), %s])", connect, process_clause(expr, arguments), mainpart)
end

function process_ip_control_fact(expr, localname, mainpart, inherited, version, sort, clausetype)
  local control_candidates = find_control_candidates(inherited)
  local fresh, dref
  -- bound discourse referent
  fresh = "'.fact'"
  freshnames[fresh] = 1
  referent = referent + 1
  -- create discourse referent
  dref = string.format("x('%s', %s)", sort, referent)
  -- increment fact for fresh fact statement
  fact = fact + 1
  if localname == "'arg0'" or localname == "'prd2'" or localname == "'prd'" then
    local arguments = {}
    return string.format("someFact(%s, 'fact%s', %s, embed(%s), %s, %s)", fresh, fact, dref, process_clause(expr, arguments, clausetype), localname, mainpart)
  else
    -- preserve subject if controller in higher clause layer
    local arguments = {}
    if version == "2" and control_candidates["arg0"] then
      -- subject control forced and there is a subject controller
      arguments["'arg0'"] = 1
      return string.format("someFact(%s, 'fact%s', %s, control2(%s), %s, %s)", fresh, fact, dref, process_clause(expr, arguments), localname, mainpart)
    elseif version == "2" then
      -- subject control forced but there is no subject controller
      return string.format("someFact(%s, 'fact%s', %s, embed(%s), %s, %s)", fresh, fact, dref, process_clause(expr, arguments), localname, mainpart)
    elseif control_candidates["arg0"] or control_candidates["arg1"] or control_candidates["arg2"] or control_candidates["h"] then
      -- basic control
      arguments["'arg0'"] = 1
      return string.format("someFact(%s, 'fact%s', %s, control(%s), %s, %s)", fresh, fact, dref, process_clause(expr, arguments), localname, mainpart)
    else
      -- no control
      return string.format("someFact(%s, 'fact%s', %s, embed(%s), %s, %s)", fresh, fact, dref, process_clause(expr, arguments), localname, mainpart)
    end
  end
end

function process_ip_embed_fact(expr, localname, mainpart, sort, clausetype)
  local fresh, dref
  -- bound discourse referent
  fresh = "'.fact'"
  freshnames[fresh] = 1
  referent = referent + 1
  -- create discourse referent
  dref = string.format("x('%s', %s)", sort, referent)
  -- reset locality
  local arguments = {}
  -- increment fact for fresh fact statement
  fact = fact + 1
  return string.format("someFact(%s, 'fact%s', %s, embed(%s), %s, %s)", fresh, fact, dref, process_clause(expr, arguments, clausetype), localname, mainpart)
end

function process_multi_sentence_fact(expr, localname, mainpart, sort)
  -- bound discourse referent
  local fresh = "'.fact'"
  freshnames[fresh] = 1
  referent = referent + 1
  -- create discourse referent
  local dref = string.format("x('%s', %s)", sort, referent)
  -- reset locality
  local discourse, discourse_args, discourse_mark = {}, {}, {}
  -- multi-sentence parts
  discourse_args[1] = "'.event'"
  for i=2,#expr do
    discourse[i-1] = string.format("'disc%s'", i-1)
    discourse_args[i] = discourse[i-1]
    discourse_mark[i] = discourse[i-1]
  end
  fact = fact + 1
  referent = referent + 1
  -- create event discourse referent
  local event_dref = string.format("x('EVENT', %s)", referent)
  -- create point for discourse collection
  local body = string.format("namely(%s, '.event', pred('discourse%s', %s))", event_dref, fact, make_ordered_list(discourse_args))
  for i = #expr, 2, -1 do
    local arguments = {}
    body = process_ip_embed_fact(expr[i], discourse_mark[i], body, "FACT")
  end
  -- increment fact for fresh fact statement
  fact = fact + 1
  return string.format("someFact(%s, 'fact%s', %s, embed(local(%s, %s)), %s, %s)", fresh, fact, dref, make_ordered_list(discourse), body, localname, mainpart)
end

function process_ip_car(expr, localname, mainpart, sort)
  -- bound discourse referent
  local fresh = "'.fact'"
  freshnames[fresh] = 1
  referent = referent + 1
  -- create discourse referent
  local dref = string.format("x('%s', %s)", sort, referent)
  -- reset locality
  local arguments = {}
  fact = fact + 1
  return string.format("someClassic_rest(%s, %s, connect('&', [pred('xxx%s', ['h']), mov('h' ,'T', embed(%s))]), %s, %s)", fresh, dref, fact, process_clause(expr, arguments), localname, mainpart)
end

function process_clause_iml(expr, arguments)
  local conn, conjn, conjs = "", 0, {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^CONJP') then
      conn = concat("_", conn, make_connrole_headword(expr[i]))
    elseif type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and type(expr[i][2]) == 'string' and string.find(expr[i][1], '^CONJ') then
      conn = concat("_", conn, expr[i][2])
    end
  end
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^IML') then
      local args = {}
      for k, v in pairs(arguments) do
        args[k] = v
      end
      conjn = conjn + 1
      conjs[conjn] = process_clause(expr[i], args)
    elseif type(expr[i]) == 'table' and type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IML') then
      local args = {}
      for k, v in pairs(arguments) do
        args[k] = v
      end
      conjn = conjn + 1
      conjs[conjn] = process_clause(expr[i][#expr[i]], args)
    end
  end
  local conjsresult = make_ordered_list(conjs)
  if conjsresult == '[]' then
    -- there were no conjuncts, so expr is treated as a single clause
    return process_clause(expr, arguments)
  else
    if conn == "" then
      -- fact = fact + 1
      -- conn = string.format("and%s", fact)
      conn = "&"
    end
    return string.format("connect('%s', %s)", conn, conjsresult)
  end
end

function process_pp_conj(expr, link, main)
  local arguments = {}
  arguments["'h'"] = 1
  -- collect information about the conjuncts
  local conn, conjn, conj_links = "", 0, {}
  for i=2,#expr do
    if type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and string.find(expr[i][1], '^CONJP') then
      conn = concat("_", conn, make_connrole_headword(expr[i]))
    elseif type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and type(expr[i][2]) == 'string' and string.find(expr[i][1], '^CONJ') then
      conn = concat("_", conn, expr[i][2])
    elseif type(expr[i]) == 'table' and type(expr[i][1]) == 'string' and type(expr[i][2]) == 'string' and string.find(expr[i][1], '^NEG') then
      conn = concat("_", conn, expr[i][2])
    end
  end
  for i=2,#expr do
    if type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
      conjn = conjn + 1
      conj_links[i] = conjn
      arguments[string.format("'%s'", concat("_", string.format("conj%s", conjn), make_connrole_headword(expr[i])))] = 1
    elseif type(expr[i][#expr[i]][1]) == 'string' and type(expr[i][#expr[i]][#expr[i][#expr[i]]][1]) == 'string' and string.find(expr[i][#expr[i]][#expr[i][#expr[i]]][1], '^NP') then
      conjn = conjn + 1
      conj_links[i] = conjn
      arguments[string.format("'%s'", concat("_", string.format("conj%s", conjn), make_connrole_headword(expr[i][#expr[i]])))] = 1
    elseif type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
      conjn = conjn + 1
      conj_links[i] = conjn
      arguments[string.format("'%s'", concat("_", string.format("conj%s", conjn), make_connrole_headword(expr[i])))] = 1
    elseif type(expr[i][#expr[i]][1]) == 'string' and type(expr[i][#expr[i]][#expr[i][#expr[i]]][1]) == 'string' and string.find(expr[i][#expr[i]][#expr[i][#expr[i]]][1], '^IP') then
      conjn = conjn + 1
      conj_links[i] = conjn
      arguments[string.format("'%s'", concat("_", string.format("conj%s", conjn), make_connrole_headword(expr[i][#expr[i]])))] = 1
    end
  end
  -- create the kernel of the conjunct contribution
  local body = string.format("pred('%s', %s)", conn, make_list(arguments, ""))
  for i = #expr, 2, -1 do
    if type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^NP') then
      body = process_np(expr[i][#expr[i]], string.format("'%s'", concat("_", string.format("conj%s", conj_links[i]), make_connrole_headword(expr[i]))), body)
    elseif type(expr[i][#expr[i]][1]) == 'string' and type(expr[i][#expr[i]][#expr[i][#expr[i]]][1]) == 'string' and string.find(expr[i][#expr[i]][#expr[i][#expr[i]]][1], '^NP') then
      body = process_np(expr[i][#expr[i]][#expr[i][#expr[i]]], string.format("'%s'", concat("_", string.format("conj%s", conj_links[i]), make_connrole_headword(expr[i][#expr[i]]))), body)
    elseif type(expr[i][#expr[i]][1]) == 'string' and string.find(expr[i][#expr[i]][1], '^IP') then
      body = process_ip_embed_fact(expr[i][#expr[i]], string.format("'%s'", concat("_", string.format("conj%s", conj_links[i]), make_connrole_headword(expr[i]))), body, "FACT")
    elseif type(expr[i][#expr[i]][1]) == 'string' and type(expr[i][#expr[i]][#expr[i][#expr[i]]][1]) == 'string' and string.find(expr[i][#expr[i]][#expr[i][#expr[i]]][1], '^IP') then
      body = process_ip_embed_fact(expr[i][#expr[i]][#expr[i][#expr[i]]], string.format("'%s'", concat("_", string.format("conj%s", conj_links[i]), make_connrole_headword(expr[i][#expr[i]]))), body, "FACT")
    end
  end
  -- add the contribution to main
  local fresh = "'@e'"
  freshnames[fresh] = 1
  referent = referent + 1
  -- create discourse referent
  local dref = string.format("x('CONJ', %s)", referent)
  return string.format("someClassic_rest(%s, %s, local(%s, %s), %s, %s)", fresh, dref, make_list(arguments, ""), body, link, main)
end

---------------------------------------------------

lpeg = require 'lpeg' -- see http://www.inf.puc-rio.br/~roberto/lpeg/

imports = 'P R S C V match'
for w in imports:gmatch('%a+') do _G[w] = lpeg[w] end -- make e.g. 'lpeg.P' function available as 'P'

function tosymbol(s) return s end
function tolist(x, ...) return {...} end -- ignore the first capture, the whole sexpr

ws = S' \t\n'^0                 -- whitespace, 0 or more

Tstring = C(P'"' * (P(1) - P'"')^0 * P'"') * ws

sep = S'()" \t\n'
symstart = (P(1) - sep)
symchar = (P(1) - sep)
Tsymbol = C(symstart * symchar^0) * ws / tosymbol

atom = Tstring + Tsymbol
lpar = P'(' * ws
rpar = P')' * ws
sexpr = P{ -- defines a recursive pattern
  'S';
  S = ws * lpar * C((atom + V'S')^0) * rpar / tolist
}

io.input(arg[1])
local text = io.read "*all"
io.input()

function alltrees ()
  local pos = 1             -- current position in text
  return function ()        -- iterator function
    while pos < #text do    -- repeat while there is text
      local w, e = string.find(text, "%(%s*%(", pos)
      if w then             -- found a tree?
        pos = e             -- next position is after this tree
        return w            -- return the tree location
      else
        return nil
      end
    end
    return nil              -- no more text: end of traversal
  end
end

local forest = {}
local count = 1
for pos in alltrees() do
  local tree = match(sexpr, text, pos)
  local node = {}
  node[1] = tree[2][2]
  node[2] = tree[1]
  node[3] = 'none'
  forest[count] = node
  count = count + 1
end

for i=1,#forest do
  freshnames, arguments, referent = {}, {}, 0
  local id, body = forest[i][1], process_clause(forest[i][2], arguments)
  if string.find(id, ';') then
    id = clean_id(string.sub(id, 1, string.find(id, ';')-1))
  else
    id = clean_id(id)
  end
  local punc = ","
  if i == #forest then
    punc = "."
  end
  print(string.format("do_it('id_%s', fresh(%s, closure('exists', %s)))%s", id, make_list(freshnames, ""), body, punc))
end

