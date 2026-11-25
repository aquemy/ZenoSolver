-- {{< node "Theorem 4.7" >}}: a link to the blueprint node of that label, with its Lean badge.
-- {{< node "Theorem 4.7" text="the converse" >}} changes the link text; badge=false drops the badge.
-- The index is site/_nodes.json, written by gen_blueprint.py from the kernel status, so a badge
-- never says more than the blueprint does. A label the blueprint leaves out (its `note_only` list:
-- refuted conjectures, counterexamples, general graphs) links to its section of the theory note on
-- GitHub, without a badge. An unknown label is an error.

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
    if not entry then error("node shortcode: no blueprint node '" .. label .. "'") end
    local text = pandoc.utils.stringify(kwargs["text"] or "")
    if text == "" then text = label end
    if entry.href then
      return pandoc.Link(text, entry.href, "In the theory note, " .. entry.where)
    end
    local link = pandoc.Link(text, blueprint_href(entry.anchor))
    if pandoc.utils.stringify(kwargs["badge"] or "") == "false" then
      return link
    end
    local badge = pandoc.Span(entry.lean, pandoc.Attr("", { "badge", entry.class }))
    return pandoc.Inlines({ link, pandoc.Space(), badge })
  end,
}
