type Option a
con Some : all a. a -> Option a
con None : all a. () -> Option a

type These a b
con This : all a. all b. a -> These a b
con That : all a. all b. b -> These a b
con These : all a. all b. (a, b) -> These a b

type Either a b
con Left: all a. all b. a -> Either a b
con Right: all a. all b. b -> Either a b
