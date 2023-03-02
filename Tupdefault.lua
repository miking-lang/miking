local sources = tup.glob('*.mc')

for _, source in ipairs(sources) do
  testsFor(source)
end
