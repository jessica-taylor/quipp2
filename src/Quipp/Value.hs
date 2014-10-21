module Quipp.Value where


data Value = DoubleValue Double | BoolValue Bool | CategoricalValue Int Int deriving (Eq, Ord, Show)
