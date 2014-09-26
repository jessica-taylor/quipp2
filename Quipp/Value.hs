module Value (Value) where


data Type = DoubleType deriving (Eq, Ord, Show)

data Value = DoubleValue Double deriving (Eq, Ord, Show)
