module Quipp.Value where

import Quipp.ExpFam


data Value = DoubleValue Double | BoolValue Bool deriving (Eq, Ord, Show)

fromDoubleValue (DoubleValue a) = a
doublePromoter = (DoubleValue, fromDoubleValue)
gaussianValueExpFam = promoteExpFam doublePromoter gaussianExpFam

boolPromoter = (BoolValue . (== 1), \(BoolValue x) -> if x then 1 else 0)
boolValueExpFam = promoteExpFam boolPromoter (categoricalExpFam 2)

