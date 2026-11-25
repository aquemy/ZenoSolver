-- {{< node "Theorem 4.5" >}}: a link to the blueprint node of that label, with its Lean badge.
-- {{< node "Theorem 4.5" text="the front" >}} changes the link text; badge=false drops the badge.
-- The labels are those of the theory note (revision 3); doc/theory/revision-3-map.md, Table C, maps
-- the labels of revision 2 to them. The index is site/_nodes.json, written by gen_blueprint.py from
-- the claim ledger and the kernel, so a badge never says more than the blueprint does. An unknown
-- label stops the render (gen_blueprint.py already lists every unknown label of the site).

local index = nil

local function load_index()
  if index then return index end
  local dir = quarto.project.directory or "."
  local f = io.open(dir .. "/_nodes.json", "r")
  if not f then error("node shortcode: _nodes.json not found; run gen_blueprint.py") end
  index = quarto.json.decode(f:read("a"))
  f:close()
  return index
end

local function blueprint_href(anchor)
  local offset = quarto.project.offset or "."
  return offset .. "/proofs.html#" .. anchor
end

return {
  ["node"] = function(args, kwargs)
    local label = pandoc.utils.stringify(args[1])
    local entry = load_index()[label]
    if not entry then
      error("node shortcode: no blueprint node '" .. label .. "' (use the labels of revision 3 of " ..
        "the theory note; doc/theory/revision-3-map.md, Table C, maps the old ones)")
    end
    local text = pandoc.utils.stringify(kwargs["text"] or "")
    if text == "" then text = label end
    local link = pandoc.Link(text, blueprint_href(entry.anchor), "Theory note, " .. (entry.where or ""))
    if pandoc.utils.stringify(kwargs["badge"] or "") == "false" then
      return link
    end
    local badge = pandoc.Span(entry.lean, pandoc.Attr("", { "badge", entry.class }))
    return pandoc.Inlines({ link, pandoc.Space(), badge })
  end,
}
