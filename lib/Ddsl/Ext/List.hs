module Ddsl.Ext.List
  ( ListMd (listName)
  , ListWit
  , listWit
  , List (..)
  , prefixMatch
  , listLength
  , sublist
  , isEmptyList
  , mkListMd
  -- * Low-level
  , prefixMatchR
  , listLengthR
  , listTheory
  , mvwListLen
  , mvwListMatch
  ) where

import Ddsl.Ext.List.Class
import Ddsl.Ext.List.TH
