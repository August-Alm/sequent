let (<<) f g x = f (g x)

let (>>) f g x = g (f x)

let (||>) (x, y) f = f x y

module StringMap = Map.Make(String)

