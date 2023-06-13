# Load data

```
?[row, op, opId, reprs, reprScope] <~ JsonReader(url: "file://./instances.json", fields: ["op", "opId", "reprs", "reprScope"], prepend_index: true)

:replace apps {row => op, opId, reprScope, reprs}
```

```
?[count(row)] := *apps{row}
```

# Wellformedness checks

```
scopes[reprScope] := *apps{reprScope}
usedIn[scopeOfRepr, scopeOfOpi] := *apps{reprScope: scopeOfOpi, reprs}, repr in reprs, scopeOfRepr = get(repr, 0)
badUses[scopeOfRepr, scopeOfOpi] := usedIn[scopeOfRepr, scopeOfOpi], scopeOfRepr > scopeOfOpi, scopes[scopeOfOpi]
?[op, reprs, reprScope] := *apps{op, reprs, reprScope}, badUses[scopeOfRepr, reprScope], repr in reprs, scopeOfRepr = get(repr, 0)
```

# Without deduping

## Apps per scope

```
appsPerScope[reprScope, count(reprScope)] := *apps{reprScope}
?[size, count(size)] := appsPerScope[_, size]
```

## Partitioning

```
edges[row, to] := *apps{row, reprs, reprScope}, repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
appsPerComp[comp, count(comp)] := components[row, comp], *apps{row}
?[size, count(size)] := appsPerComp[_, size]
```

## Repr use counts

```
uses[row, repr] := *apps{row, reprs}, pair in reprs, repr = get(pair, 1)
degree[repr, count(row)] := uses[row, repr]
?[size, count(size)] := degree[_, size]
```

## References to reprs outside current scope

```
outsideRefs[selfScope, repr] := *apps{reprScope: selfScope, reprs}, r in reprs, get(r, 0) < selfScope, repr = get(r, 1)
counts[scope, count(repr)] := outsideRefs[scope, repr]
?[size, count(size)] := counts[_, size]
```

## References to reprs outside current scope taking partitioning into account

```
edges[row, to] := *apps{row, reprs, reprScope}, repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
outsideRefs[selfScope, comp, repr] := components[row, comp], *apps{row, reprScope: selfScope, reprs}, r in reprs, get(r, 0) < selfScope, repr = get(r, 1)
counts[scope, comp, count(repr)] := outsideRefs[scope, comp, repr]
?[size, count(size)] := counts[_, _, size]
```

# With simple dedup

## Apps per scope

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
appsPerScope[reprScope, count(reprScope)] := deduped[_, _, reprScope, _]
?[size, count(size)] := appsPerScope[_, size]
```

## Partitioning

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
edges[row, to] := deduped[row, op, reprScope, reprs], repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
appsPerComp[comp, count(comp)] := components[row, comp], *apps{row}
?[size, count(size)] := appsPerComp[_, size]
```

## Partitions above a certain size

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
edges[row, to] := deduped[row, op, reprScope, reprs], repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
appsPerComp[comp, count(comp)] := components[row, comp], *apps{row}
sizes[size] := appsPerComp[_, size]
?[lower_bound, count(size)] := sizes[lower_bound], appsPerComp[_, size], lower_bound <= size
```

## Edges in largest component

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
edges[row, to] := deduped[row, op, reprScope, reprs], repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
appsPerComp[comp, count(comp)] := components[row, comp], *apps{row}
maxSize[max(size)] := appsPerComp[_, size]
largestComp[comp] := maxSize[size], appsPerComp[comp, size]
?[row, collect(r), op] := largestComp[comp], components[row, comp], *apps{row, op, reprs}, repr in reprs, r = get(repr, 1)
```

## Edges in components whose size is in a range

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
edges[row, to] := deduped[row, op, reprScope, reprs], repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
appsPerComp[comp, count(comp)] := components[row, comp], *apps{row}
chosenComps[comp] := appsPerComp[comp, size], 152 <= size, size <= 152
?[row, collect(r), op] := chosenComps[comp], components[row, comp], *apps{row, op, reprs}, repr in reprs, r = get(repr, 1)
```

## Repr use counts

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
uses[row, repr] := deduped[row, _, _, reprs], pair in reprs, repr = get(pair, 1)
degree[repr, count(row)] := uses[row, repr]
?[size, count(size)] := degree[_, size]
```

## External repr references and app count per partition

```
deduped[choice(row), op, reprScope, reprs] := *apps{row, op, reprs, reprScope}
edges[row, to] := deduped[row, op, reprScope, reprs], repr in reprs, to = [reprScope, repr]
components[row, comp] <~ ConnectedComponents(edges[from, to])
appsPerComp[comp, count(comp)] := components[row, comp], *apps{row}
outsideRefs[selfScope, comp, repr] := components[row, comp], *apps{row, reprScope: selfScope, reprs}, r in reprs, get(r, 0) < selfScope, repr = get(r, 1)
refsPerComp[comp, count(comp)] := outsideRefs[_, comp, _]
?[refs, apps, count(comp)] := appsPerComp[comp, apps], refsPerComp[comp, refs]
```
