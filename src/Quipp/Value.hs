module Quipp.Value where


data Value = DoubleValue Double | BoolValue Bool deriving (Eq, Ord, Show)
