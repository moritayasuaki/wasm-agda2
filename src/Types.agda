module Types where

infix 4.5 _⇒_
record arrow (I : Set) (O : Set) : Set where
  constructor _⇒_
  field
    dom : I
    cod : O
