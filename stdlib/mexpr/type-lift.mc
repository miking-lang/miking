-- Lift out types of an MExpr program. In particular, record types are lifted
-- and replaced with type variables, and all constructors for variant types are
-- lifted and collected into a single type.  Note that the latter probably has
-- consequences for type checking: information is lost when lifting constructor
-- definitions.
--
-- Requires symbolize and type-annot to be run first.

-----------------
-- ENVIRONMENT --
-----------------
-- * Associative sequence of tuples of type aliases. I cannot use AssocMap since there may be internal dependencies.
-- * [Records] Map from currently defined records to their type names.
-- * [Variants] Map from variant type names to their current constructors.

-----------
-- TERMS --
-----------


-----------
-- TYPES --
-----------
