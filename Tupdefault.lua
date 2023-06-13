local sources = tup.glob('*.mc')
for _, source in ipairs(sources) do
  testsFor(source)
end

local syns = tup.glob('*.syn')
for _, source in ipairs(syns) do
  miSyn(source, '%B.mc')
end
