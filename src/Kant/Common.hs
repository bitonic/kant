module Kant.Common (trim) where

import           Data.Char (isSpace)

trim :: String -> String
trim = reverse . f . reverse . f where f = dropWhile isSpace

