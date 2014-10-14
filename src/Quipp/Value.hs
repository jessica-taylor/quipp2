module Quipp.Value where


data Value = DoubleValue Double | CategoricalValue Int deriving (Eq, Ord, Show)
