# notes

## Todo items
- General things:
    - Consistent casing.
    - New params on new lines?
- Definition things:
    - `ExposedFace` and `DirectionExposingFace` correspond to the same object, but the latter is defined in terms of the support function.
    - `SupportFun` make sure coersion is correct, it typechecks but maybe just encode it explicitly.
    - `epigraph` and `stricEpigraph` coersions from Real to EReal.
    - `InConvRn` and `InProperConvRn` define set of convex functions mappping to Real \cup +infinity and [-infinity, +infinity], respectively. Maybe consolidate the two defs.
    - `AsymptoticFun`
    - `IsNondegenerate` double check usage is for EReals or WithTop \R.
    - `IsKPosHomogeneous` check raising to a real power `t ^ k`.
    - The section on subgradients is for convex f, now the question is whether this constraint should be encoded in the defs.
    - `Biconjugate`