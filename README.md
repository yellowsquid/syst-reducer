# System T Self-Reducer

A fuelled self-reducer for System T embedded in Idris 2

# Code Structure

- `Term.idr` :: Deep embedding of System T terms, using co-deBruijn variable bindings.
- `Term/Syntax.idr` :: Smart constructors for System T terms, doing some simplification.
- `Encodings/` :: Encodings of various types.
