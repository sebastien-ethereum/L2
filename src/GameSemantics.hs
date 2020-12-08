--------------------------------------------------------------------------------
--
-- Game semantics for MALLP (multiplicative additive linear logic, polarized)
--
-- Author: sebastien@ethereum.org
--
--------------------------------------------------------------------------------

module GameSemantics where

import Control.Monad

---- Formulas ----

data Formula
  = PositiveFormula PositiveFormula
  | NegativeFormula NegativeFormula

data PositiveFormula
  = -- linear shift
    ShiftDown NegativeFormula
  | -- multiplicative conjunction
    Tensor PositiveFormula PositiveFormula
  | -- multiplicative truth
    One
  | -- additive disjunction
    Plus PositiveFormula PositiveFormula
  | -- additive falsehood
    Zero

data NegativeFormula
  = -- linear shift
    ShiftUp PositiveFormula
  | -- multiplicative disjunction
    Par NegativeFormula NegativeFormula
  | -- multiplicative falsehood
    Bottom
  | -- additive conjunction
    With NegativeFormula NegativeFormula
  | -- additive truth
    Top

data PositiveBias
  = Bias_ShiftDown
  | Bias_Tensor1 PositiveBias
  | Bias_Tensor2 PositiveBias
  | Bias_Plus1 PositiveBias
  | Bias_Plus2 PositiveBias
  deriving (Eq)

data NegativeBias
  = Bias_ShiftUp
  | Bias_Par1 NegativeBias
  | Bias_Par2 NegativeBias
  | Bias_With1 NegativeBias
  | Bias_With2 NegativeBias
  deriving (Eq)

data PositiveLocus
  = PositiveRootLocus
  | PositiveSubLocus NegativeLocus NegativeBias
  deriving (Eq)

data NegativeLocus
  = NegativeRootLocus
  | NegativeSubLocus PositiveLocus PositiveBias
  deriving (Eq)

positiveSubFormula :: PositiveLocus -> Formula -> Maybe PositiveFormula
positiveSubFormula posLocus formula =
  case posLocus of
    PositiveRootLocus ->
      case formula of
        PositiveFormula posFormula ->
          Just posFormula
        NegativeFormula _ ->
          Nothing
    PositiveSubLocus negLocus negBias -> do
      negFormula <- negativeSubFormula negLocus formula
      positiveSubFormula1 negBias negFormula
  where
    positiveSubFormula1 negBias negFormula =
      case (negBias, negFormula) of
        (Bias_ShiftUp, ShiftUp posFormula) ->
          Just posFormula
        (Bias_Par1 negBias', Par negFormula' _) ->
          positiveSubFormula1 negBias' negFormula'
        (Bias_Par2 negBias', Par _ negFormula') ->
          positiveSubFormula1 negBias' negFormula'
        (Bias_With1 negBias', With negFormula' _) ->
          positiveSubFormula1 negBias' negFormula'
        (Bias_With2 negBias', With _ negFormula') ->
          positiveSubFormula1 negBias' negFormula'
        (_, _) ->
          Nothing

negativeSubFormula :: NegativeLocus -> Formula -> Maybe NegativeFormula
negativeSubFormula negLocus formula =
  case negLocus of
    NegativeRootLocus ->
      case formula of
        NegativeFormula negFormula ->
          Just negFormula
        PositiveFormula _ ->
          Nothing
    NegativeSubLocus posLocus posBias -> do
      posFormula <- positiveSubFormula posLocus formula
      negativeSubFormula1 posBias posFormula
  where
    negativeSubFormula1 posBias posFormula =
      case (posBias, posFormula) of
        (Bias_ShiftDown, ShiftDown negFormula) ->
          Just negFormula
        (Bias_Tensor1 posBias', Tensor posFormula' _) ->
          negativeSubFormula1 posBias' posFormula'
        (Bias_Tensor2 posBias', Tensor _ posFormula') ->
          negativeSubFormula1 posBias' posFormula'
        (Bias_Plus1 posBias', Plus posFormula' _) ->
          negativeSubFormula1 posBias' posFormula'
        (Bias_Plus2 posBias', Plus _ posFormula') ->
          negativeSubFormula1 posBias' posFormula'
        _ ->
          Nothing

---- Patterns ----

data ProofPattern
  = Pattern_ShiftDown
  | Pattern_Tensor ProofPattern ProofPattern
  | Pattern_One
  | Pattern_Plus1 ProofPattern
  | Pattern_Plus2 ProofPattern
  deriving (Eq)

data RefutationPattern
  = Pattern_ShiftUp
  | Pattern_Par RefutationPattern RefutationPattern
  | Pattern_Bottom
  | Pattern_With1 RefutationPattern
  | Pattern_With2 RefutationPattern
  deriving (Eq)

isProofPatternFor :: ProofPattern -> PositiveFormula -> Bool
isProofPatternFor prfPattern posFormula =
  case (prfPattern, posFormula) of
    (Pattern_ShiftDown, ShiftDown _) ->
      True
    (Pattern_Tensor prfPattern1 prfPattern2, Tensor posFormula1 posFormula2) ->
      True
        && prfPattern1 `isProofPatternFor` posFormula1
        && prfPattern2 `isProofPatternFor` posFormula2
    (Pattern_One, One) ->
      True
    (Pattern_Plus1 prfPattern', Plus posFormula' _) ->
      True
        && prfPattern' `isProofPatternFor` posFormula'
    (Pattern_Plus2 prfPattern', Plus _ posFormula') ->
      True
        && prfPattern' `isProofPatternFor` posFormula'
    (_, _) ->
      False

isRefutationPatternFor :: RefutationPattern -> NegativeFormula -> Bool
isRefutationPatternFor rftPattern negFormula =
  case (rftPattern, negFormula) of
    (Pattern_ShiftUp, ShiftUp _) ->
      True
    (Pattern_Par rftPattern1 rftPattern2, Par negFormula1 negFormula2) ->
      True
        && rftPattern1 `isRefutationPatternFor` negFormula1
        && rftPattern2 `isRefutationPatternFor` negFormula2
    (Pattern_Bottom, Bottom) ->
      True
    (Pattern_With1 rftPattern', With negFormula' _) ->
      True
        && rftPattern' `isRefutationPatternFor` negFormula'
    (Pattern_With2 rftPattern', With _ negFormula') ->
      True
        && rftPattern' `isRefutationPatternFor` negFormula'
    (_, _) ->
      False

positiveRamification :: ProofPattern -> [PositiveBias]
positiveRamification prfPattern =
  case prfPattern of
    Pattern_ShiftDown ->
      []
        ++ [Bias_ShiftDown]
    Pattern_Tensor prfPattern1 prfPattern2 ->
      []
        ++ map Bias_Tensor1 (positiveRamification prfPattern1)
        ++ map Bias_Tensor2 (positiveRamification prfPattern2)
    Pattern_One ->
      []
    Pattern_Plus1 prfPattern' ->
      []
        ++ map Bias_Plus1 (positiveRamification prfPattern')
    Pattern_Plus2 prfPattern' ->
      []
        ++ map Bias_Plus2 (positiveRamification prfPattern')

negativeRamification :: RefutationPattern -> [NegativeBias]
negativeRamification rftPattern =
  case rftPattern of
    Pattern_ShiftUp ->
      []
        ++ [Bias_ShiftUp]
    Pattern_Par rftPattern1 rftPattern2 ->
      []
        ++ map Bias_Par1 (negativeRamification rftPattern1)
        ++ map Bias_Par2 (negativeRamification rftPattern2)
    Pattern_Bottom ->
      []
    Pattern_With1 rftPattern' ->
      []
        ++ map Bias_With1 (negativeRamification rftPattern')
    Pattern_With2 rftPattern' ->
      []
        ++ map Bias_With2 (negativeRamification rftPattern')

---- Moves ----

type ProponentMove =
  (PositiveLocus, ProofPattern)

type OpponentMove =
  (NegativeLocus, RefutationPattern)

isInitialProponentMove :: ProponentMove -> Formula -> Bool
isInitialProponentMove proMove formula =
  case proMove of
    (posLocus, prfPattern) ->
      case posLocus of
        PositiveRootLocus ->
          maybe False (prfPattern `isProofPatternFor`) (positiveSubFormula posLocus formula)
        PositiveSubLocus _ _ ->
          False

isInitialOpponentMove :: OpponentMove -> Formula -> Bool
isInitialOpponentMove opMove formula =
  case opMove of
    (negLocus, rftPattern) ->
      case negLocus of
        NegativeRootLocus ->
          maybe False (rftPattern `isRefutationPatternFor`) (negativeSubFormula negLocus formula)
        NegativeSubLocus _ _ ->
          False

isProponentMoveJustifedByOpponentMove :: ProponentMove -> OpponentMove -> Formula -> Bool
isProponentMoveJustifedByOpponentMove proMove opMove formula =
  case (opMove, proMove) of
    ((negLocus, rftPattern), (posLocus, prfPattern)) ->
      case posLocus of
        PositiveRootLocus ->
          False
        PositiveSubLocus negLocus' negBias ->
          True
            && negLocus == negLocus'
            && negBias `elem` negativeRamification rftPattern
            && maybe False (prfPattern `isProofPatternFor`) (positiveSubFormula posLocus formula)

isOpponentMoveJustifiedByProponentMove :: OpponentMove -> ProponentMove -> Formula -> Bool
isOpponentMoveJustifiedByProponentMove opMove proMove formula =
  case (proMove, opMove) of
    ((posLocus, prfPattern), (negLocus, rftPattern)) ->
      case negLocus of
        NegativeRootLocus ->
          False
        NegativeSubLocus posLocus' posBias ->
          True
            && posLocus == posLocus'
            && posBias `elem` positiveRamification prfPattern
            && maybe False (rftPattern `isRefutationPatternFor`) (negativeSubFormula negLocus formula)

---- Positions ----

data Position
  = ProponentPosition ProponentPosition
  | OpponentPosition OpponentPosition

data ProponentPosition
  = ProponentRootPosition
  | ProponentSubPosition OpponentPosition OpponentMove

data OpponentPosition
  = OpponentRootPosition
  | OpponentSubPosition ProponentPosition ProponentMove

initialProponentPosition :: ProponentPosition
initialProponentPosition =
  ProponentRootPosition

initialOpponentPosition :: OpponentPosition
initialOpponentPosition =
  OpponentRootPosition

minimalPrefixOfProponentPositionJustifyingProponentMove :: ProponentPosition -> ProponentMove -> Formula -> Maybe ProponentPosition
minimalPrefixOfProponentPositionJustifyingProponentMove proPosition proMove formula =
  if isInitialProponentMove proMove formula
    then Just ProponentRootPosition
    else case proPosition of
      ProponentRootPosition ->
        Nothing
      ProponentSubPosition opPosition' opMove ->
        if (proMove `isProponentMoveJustifedByOpponentMove` opMove) formula
          then Just proPosition
          else case opPosition' of
            OpponentRootPosition ->
              Nothing
            OpponentSubPosition proPosition' _ ->
              minimalPrefixOfProponentPositionJustifyingProponentMove proPosition' proMove formula

minimalPrefixOfOpponentPositionJustifyingOpponentMove :: OpponentPosition -> OpponentMove -> Formula -> Maybe OpponentPosition
minimalPrefixOfOpponentPositionJustifyingOpponentMove opPosition opMove formula =
  if isInitialOpponentMove opMove formula
    then Just OpponentRootPosition
    else case opPosition of
      OpponentRootPosition ->
        Nothing
      OpponentSubPosition proPosition' proMove ->
        if (opMove `isOpponentMoveJustifiedByProponentMove` proMove) formula
          then Just opPosition
          else case proPosition' of
            ProponentRootPosition ->
              Nothing
            ProponentSubPosition opPosition' _ ->
              minimalPrefixOfOpponentPositionJustifyingOpponentMove opPosition' opMove formula

proponentViewOfProponentPosition :: ProponentPosition -> Formula -> ProponentPosition
proponentViewOfProponentPosition proPosition =
  case proPosition of
    ProponentRootPosition -> do
      return ProponentRootPosition
    ProponentSubPosition opPosition opMove -> do
      opPosition' <- maybe (error "illegal position") id <$> minimalPrefixOfOpponentPositionJustifyingOpponentMove opPosition opMove
      opPosition'' <- proponentViewOfOpponentPosition opPosition'
      return (ProponentSubPosition opPosition'' opMove)

proponentViewOfOpponentPosition :: OpponentPosition -> Formula -> OpponentPosition
proponentViewOfOpponentPosition opPosition =
  case opPosition of
    OpponentRootPosition -> do
      return OpponentRootPosition
    OpponentSubPosition proPosition proMove -> do
      proPosition' <- proponentViewOfProponentPosition proPosition
      return (OpponentSubPosition proPosition' proMove)

opponentViewOfOpponentPosition :: OpponentPosition -> Formula -> OpponentPosition
opponentViewOfOpponentPosition opPosition =
  case opPosition of
    OpponentRootPosition -> do
      return OpponentRootPosition
    OpponentSubPosition proPosition proMove -> do
      proPosition' <- maybe (error "illegal position") id <$> minimalPrefixOfProponentPositionJustifyingProponentMove proPosition proMove
      proPosition'' <- opponentViewOfProponentPosition proPosition'
      return (OpponentSubPosition proPosition'' proMove)

opponentViewOfProponentPosition :: ProponentPosition -> Formula -> ProponentPosition
opponentViewOfProponentPosition proPosition =
  case proPosition of
    ProponentRootPosition -> do
      return ProponentRootPosition
    ProponentSubPosition opPosition opMove -> do
      opPosition' <- opponentViewOfOpponentPosition opPosition
      return (ProponentSubPosition opPosition' opMove)

isJustifiedProponentMove :: ProponentPosition -> ProponentMove -> Formula -> Bool
isJustifiedProponentMove proPosition proMove = do
  proView <- proponentViewOfProponentPosition proPosition
  maybe False (const True) <$> minimalPrefixOfProponentPositionJustifyingProponentMove proView proMove

isJustifiedOpponentMove :: OpponentPosition -> OpponentMove -> Formula -> Bool
isJustifiedOpponentMove opPosition opMove = do
  opView <- opponentViewOfOpponentPosition opPosition
  maybe False (const True) <$> minimalPrefixOfOpponentPositionJustifyingOpponentMove opView opMove

isLinearProponentMove :: ProponentPosition -> ProponentMove -> Formula -> Bool
isLinearProponentMove proPosition proMove = do
  case (proPosition, proMove) of
    (ProponentRootPosition, _) ->
      return True
    (ProponentSubPosition OpponentRootPosition _, _) ->
      return True
    (ProponentSubPosition (OpponentSubPosition proPosition' (posLocus', _)) _, (posLocus, _)) ->
      if posLocus /= posLocus'
        then isLinearProponentMove proPosition' proMove
        else return False

isLinearOpponentMove :: OpponentPosition -> OpponentMove -> Formula -> Bool
isLinearOpponentMove opPosition opMove = do
  case (opPosition, opMove) of
    (OpponentRootPosition, _) ->
      return True
    (OpponentSubPosition ProponentRootPosition _, _) ->
      return True
    (OpponentSubPosition (ProponentSubPosition opPosition' (opLocus', _)) _, (opLocus, _)) ->
      if opLocus /= opLocus'
        then isLinearOpponentMove opPosition' opMove
        else return False

isLegalProponentMove :: ProponentPosition -> ProponentMove -> Formula -> Bool
isLegalProponentMove proPosition proMove formula =
  True
    && isJustifiedProponentMove proPosition proMove formula
    && isLinearProponentMove proPosition proMove formula

isLegalOpponentMove :: OpponentPosition -> OpponentMove -> Formula -> Bool
isLegalOpponentMove opPosition opMove formula =
  True
    && isJustifiedOpponentMove opPosition opMove formula
    && isLinearOpponentMove opPosition opMove formula

playProponentMove :: ProponentPosition -> ProponentMove -> Formula -> Maybe OpponentPosition
playProponentMove proPosition proMove formula =
  if isLegalProponentMove proPosition proMove formula
    then Just (OpponentSubPosition proPosition proMove)
    else Nothing

playOpponentMove :: OpponentPosition -> OpponentMove -> Formula -> Maybe ProponentPosition
playOpponentMove opPosition opMove formula =
  if isLegalOpponentMove opPosition opMove formula
    then Just (ProponentSubPosition opPosition opMove)
    else Nothing

---- Proponent Strategies ----

data ProponentDerivation
  = ProponentDerivationOfContext_ ProponentDerivationOfContext
  | ProponentDerivationOfContradiction_ ProponentDerivationOfContradiction

data ProponentDerivationOfTrivial
  = ProponentDerivationOfTrivial ProofPattern ProponentDerivationOfContext

data ProponentDerivationOfContext
  = ProponentDerivationOfContext [(NegativeLocus, ProponentDerivationOfTrue)]

data ProponentDerivationOfTrue
  = ProponentDerivationOfTrue [(RefutationPattern, ProponentDerivationOfContradiction)]

data ProponentDerivationOfContradiction
  = ProponentDerivationOfContradiction PositiveLocus ProponentDerivationOfTrivial

proponentSubDerivationForProponentPosition :: ProponentDerivation -> ProponentPosition -> Maybe ProponentDerivationOfContradiction
proponentSubDerivationForProponentPosition proDerivation proPosition =
  case proPosition of
    ProponentRootPosition ->
      case proDerivation of
        ProponentDerivationOfContext_ _ ->
          Nothing
        ProponentDerivationOfContradiction_ proContradiction ->
          Just proContradiction
    ProponentSubPosition opPosition opMove -> do
      case opMove of
        (negLocus, rftPattern) -> do
          proContext <- proponentSubDerivationForOpponentPosition proDerivation opPosition
          case proContext of
            ProponentDerivationOfContext negLocusBranches -> do
              proTrue <- lookup negLocus negLocusBranches
              case proTrue of
                ProponentDerivationOfTrue rftPatternBranches -> do
                  proContradiction <- lookup rftPattern rftPatternBranches
                  Just proContradiction

proponentSubDerivationForOpponentPosition :: ProponentDerivation -> OpponentPosition -> Maybe ProponentDerivationOfContext
proponentSubDerivationForOpponentPosition proDerivation opPosition =
  case opPosition of
    OpponentRootPosition ->
      case proDerivation of
        ProponentDerivationOfContext_ proContext ->
          Just proContext
        ProponentDerivationOfContradiction_ _ ->
          Nothing
    OpponentSubPosition proPosition proMove -> do
      case proMove of
        (posLocus, prfPattern) -> do
          proContradiction <- proponentSubDerivationForProponentPosition proDerivation proPosition
          case proContradiction of
            ProponentDerivationOfContradiction posLocus' proTrivial -> do
              guard (posLocus == posLocus')
              case proTrivial of
                ProponentDerivationOfTrivial prfPattern' proContext -> do
                  guard (prfPattern == prfPattern')
                  Just proContext

proponentStrategy :: ProponentDerivation -> ProponentPosition -> Maybe ProponentMove
proponentStrategy proDerivation proPosition = do
  proContradiction <- proponentSubDerivationForProponentPosition proDerivation proPosition
  case proContradiction of
    ProponentDerivationOfContradiction posLocus proTrivial -> do
      case proTrivial of
        ProponentDerivationOfTrivial prfPattern _ -> do
          Just (posLocus, prfPattern)

---- Opponent Strategies ----

data OpponentDerivation
  = OpponentDerivationOfContext_ OpponentDerivationOfContext
  | OpponentDerivationOfContradiction_ OpponentDerivationOfContradiction

data OpponentDerivationOfAbsurd
  = OpponentDerivationOfAbsurd RefutationPattern OpponentDerivationOfContext

data OpponentDerivationOfContext
  = OpponentDerivationOfContext [(PositiveLocus, OpponentDerivationOfFalse)]

data OpponentDerivationOfFalse
  = OpponentDerivationOfFalse [(ProofPattern, OpponentDerivationOfContradiction)]

data OpponentDerivationOfContradiction
  = OpponentDerivationOfContradiction NegativeLocus OpponentDerivationOfAbsurd

opponentSubDerivationForOpponentPosition :: OpponentDerivation -> OpponentPosition -> Maybe OpponentDerivationOfContradiction
opponentSubDerivationForOpponentPosition opDerivation opPosition =
  case opPosition of
    OpponentRootPosition ->
      case opDerivation of
        OpponentDerivationOfContext_ _ ->
          Nothing
        OpponentDerivationOfContradiction_ opContradiction ->
          Just opContradiction
    OpponentSubPosition proPosition proMove -> do
      case proMove of
        (posLocus, prfPattern) -> do
          opContext <- opponentSubDerivationForProponentPosition opDerivation proPosition
          case opContext of
            OpponentDerivationOfContext posLocusBranches -> do
              opFalse <- lookup posLocus posLocusBranches
              case opFalse of
                OpponentDerivationOfFalse prfPatternBranches -> do
                  opContradiction <- lookup prfPattern prfPatternBranches
                  Just opContradiction

opponentSubDerivationForProponentPosition :: OpponentDerivation -> ProponentPosition -> Maybe OpponentDerivationOfContext
opponentSubDerivationForProponentPosition opDerivation proPosition =
  case proPosition of
    ProponentRootPosition ->
      case opDerivation of
        OpponentDerivationOfContext_ opContext ->
          Just opContext
        OpponentDerivationOfContradiction_ _ ->
          Nothing
    ProponentSubPosition opPosition opMove -> do
      case opMove of
        (negLocus, rftPattern) -> do
          opContradiction <- opponentSubDerivationForOpponentPosition opDerivation opPosition
          case opContradiction of
            OpponentDerivationOfContradiction negLocus' opAbsurd -> do
              guard (negLocus == negLocus')
              case opAbsurd of
                OpponentDerivationOfAbsurd rftPattern' opContext -> do
                  guard (rftPattern == rftPattern')
                  Just opContext

opponentStrategy :: OpponentDerivation -> OpponentPosition -> Maybe OpponentMove
opponentStrategy opDerivation opPosition = do
  opContradiction <- opponentSubDerivationForOpponentPosition opDerivation opPosition
  case opContradiction of
    OpponentDerivationOfContradiction negLocus opAbsurd -> do
      case opAbsurd of
        OpponentDerivationOfAbsurd rftPattern _ -> do
          Just (negLocus, rftPattern)
