{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-
Copyright (C) 2006-2017 John MacFarlane <jgm@berkeley.edu>

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
-}

{- |
   Module      : Text.Pandoc.Readers.LaTeX
   Copyright   : Copyright (C) 2006-2017 John MacFarlane
   License     : GNU GPL, version 2 or above

   Maintainer  : John MacFarlane <jgm@berkeley.edu>
   Stability   : alpha
   Portability : portable

Conversion of LaTeX to 'Pandoc' document.

-}
module Text.Pandoc.Readers.LaTeX ( readLaTeX,
                                   applyMacros,
                                   rawLaTeXInline,
                                   rawLaTeXBlock,
                                   inlineCommand
                                 ) where

import Control.Applicative (many, optional, (<|>))
import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Trans (lift)
import Data.Char (chr, isAlphaNum, isLetter, ord, isDigit)
import Data.Default
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.Maybe (fromMaybe, maybeToList)
import Safe (minimumDef)
import System.FilePath (addExtension, replaceExtension, takeExtension)
import Text.Pandoc.Builder
import Text.Pandoc.Class (PandocMonad, PandocPure, lookupEnv, readFileFromDirs,
                          report, setResourcePath, getResourcePath)
import Text.Pandoc.Highlighting (fromListingsLanguage, languagesByExtension)
import Text.Pandoc.ImageSize (numUnit, showFl)
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.Pandoc.Parsing hiding (many, optional, withRaw,
                            mathInline, mathDisplay,
                            space, (<|>), spaces, blankline)
import Text.Pandoc.Shared
import Text.Pandoc.Readers.LaTeX.Types (Macro(..), Tok(..),
                            TokType(..), DefMacroArg(..))
import Text.Pandoc.Walk
import Text.Pandoc.Error (PandocError(PandocParsecError, PandocMacroLoop))

-- for debugging:
-- import Text.Pandoc.Extensions (getDefaultExtensions)
-- import Text.Pandoc.Class (runIOorExplode, PandocIO)
import Debug.Trace (traceShowId, trace)

-- | Parse LaTeX from string and return 'Pandoc' document.
readLaTeX :: PandocMonad m
          => ReaderOptions -- ^ Reader options
          -> Text        -- ^ String to parse (assumes @'\n'@ line endings)
          -> m Pandoc
readLaTeX opts ltx = do
  parsed <- runParserT parseLaTeX def{ sOptions = opts } "source"
               (tokenize (crFilter ltx))
  case parsed of
    Right result -> return result
    Left e       -> throwError $ PandocParsecError (T.unpack ltx) e

parseLaTeX :: PandocMonad m => LP m Pandoc
parseLaTeX = do
  bs <- blocks
  eof
  st <- getState
  let meta = sMeta st
  let doc' = doc bs
  let headerLevel (Header n _ _) = [n]
      headerLevel _ = []
  let bottomLevel = minimumDef 1 $ query headerLevel doc'
  let adjustHeaders m (Header n attr ils) = Header (n+m) attr ils
      adjustHeaders _ x = x
  let (Pandoc _ bs') =
       -- handle the case where you have \part or \chapter
       (if bottomLevel < 1
           then walk (adjustHeaders (1 - bottomLevel))
           else id) doc'
  return $ Pandoc meta bs'

-- testParser :: LP PandocIO a -> Text -> IO a
-- testParser p t = do
--   res <- runIOorExplode (runParserT p defaultLaTeXState{
--             sOptions = def{ readerExtensions =
--               enableExtension Ext_raw_tex $
--                 getDefaultExtensions "latex" }} "source" (tokenize t))
--   case res of
--        Left e  -> error (show e)
--        Right r -> return r

data LaTeXState = LaTeXState{ sOptions       :: ReaderOptions
                            , sMeta          :: Meta
                            , sQuoteContext  :: QuoteContext
                            , sMacros        :: M.Map Text Macro
                            , sContainers    :: [String]
                            , sHeaders       :: M.Map Inlines String
                            , sLogMessages   :: [LogMessage]
                            , sIdentifiers   :: Set.Set String
                            , sVerbatimMode  :: Bool
                            , sCaption       :: Maybe Inlines
                            , sInListItem    :: Bool
                            , sInTableCell   :: Bool
                            }
     deriving Show

defaultLaTeXState :: LaTeXState
defaultLaTeXState = LaTeXState{ sOptions       = def
                              , sMeta          = nullMeta
                              , sQuoteContext  = NoQuote
                              , sMacros        = M.empty
                              , sContainers    = []
                              , sHeaders       = M.empty
                              , sLogMessages   = []
                              , sIdentifiers   = Set.empty
                              , sVerbatimMode  = False
                              , sCaption       = Nothing
                              , sInListItem    = False
                              , sInTableCell   = False
                              }

instance PandocMonad m => HasQuoteContext LaTeXState m where
  getQuoteContext = sQuoteContext <$> getState
  withQuoteContext context parser = do
    oldState <- getState
    let oldQuoteContext = sQuoteContext oldState
    setState oldState { sQuoteContext = context }
    result <- parser
    newState <- getState
    setState newState { sQuoteContext = oldQuoteContext }
    return result

instance HasLogMessages LaTeXState where
  addLogMessage msg st = st{ sLogMessages = msg : sLogMessages st }
  getLogMessages st = reverse $ sLogMessages st

instance HasIdentifierList LaTeXState where
  extractIdentifierList     = sIdentifiers
  updateIdentifierList f st = st{ sIdentifiers = f $ sIdentifiers st }

instance HasIncludeFiles LaTeXState where
  getIncludeFiles = sContainers
  addIncludeFile f s = s{ sContainers = f : sContainers s }
  dropLatestIncludeFile s = s { sContainers = drop 1 $ sContainers s }

instance HasHeaderMap LaTeXState where
  extractHeaderMap     = sHeaders
  updateHeaderMap f st = st{ sHeaders = f $ sHeaders st }

instance HasMacros LaTeXState where
  extractMacros  st  = sMacros st
  updateMacros f st  = st{ sMacros = f (sMacros st) }

instance HasReaderOptions LaTeXState where
  extractReaderOptions = sOptions

instance HasMeta LaTeXState where
  setMeta field val st =
    st{ sMeta = setMeta field val $ sMeta st }
  deleteMeta field st =
    st{ sMeta = deleteMeta field $ sMeta st }

instance Default LaTeXState where
  def = defaultLaTeXState

type LP m = ParserT [Tok] LaTeXState m

withVerbatimMode :: PandocMonad m => LP m a -> LP m a
withVerbatimMode parser = do
  updateState $ \st -> st{ sVerbatimMode = True }
  result <- parser
  updateState $ \st -> st{ sVerbatimMode = False }
  return result

rawLaTeXParser :: (PandocMonad m, HasMacros s, HasReaderOptions s)
               => LP m a -> ParserT String s m String
rawLaTeXParser parser = do
  inp <- getInput
  let toks = tokenize $ T.pack inp
  pstate <- getState
  let lstate = def{ sOptions = extractReaderOptions pstate }
  res <- lift $ runParserT ((,) <$> try (snd <$> withRaw parser) <*> getState)
            lstate "source" toks
  case res of
       Left _    -> mzero
       Right (raw, st) -> do
         updateState (updateMacros ((sMacros st) <>))
         takeP (T.length (untokenize raw))

applyMacros :: (PandocMonad m, HasMacros s, HasReaderOptions s)
            => String -> ParserT String s m String
applyMacros s = (guardDisabled Ext_latex_macros >> return s) <|>
   do let retokenize = doMacros 0 *>
             (toksToString <$> many (satisfyTok (const True)))
      pstate <- getState
      let lstate = def{ sOptions = extractReaderOptions pstate
                      , sMacros  = extractMacros pstate }
      res <- runParserT retokenize lstate "math" (tokenize (T.pack s))
      case res of
           Left e -> fail (show e)
           Right s' -> return s'

rawLaTeXBlock :: (PandocMonad m, HasMacros s, HasReaderOptions s)
              => ParserT String s m String
rawLaTeXBlock = do
  lookAhead (try (char '\\' >> letter))
  rawLaTeXParser (environment <|> macroDef <|> blockCommand)

rawLaTeXInline :: (PandocMonad m, HasMacros s, HasReaderOptions s)
               => ParserT String s m String
rawLaTeXInline = do
  lookAhead (try (char '\\' >> letter) <|> char '$')
  rawLaTeXParser (inlineEnvironment <|> inlineCommand')

inlineCommand :: PandocMonad m => ParserT String ParserState m Inlines
inlineCommand = do
  lookAhead (try (char '\\' >> letter) <|> char '$')
  inp <- getInput
  let toks = tokenize $ T.pack inp
  let rawinline = do
         (il, raw) <- try $ withRaw (inlineEnvironment <|> inlineCommand')
         st <- getState
         return (il, raw, st)
  pstate <- getState
  let lstate = def{ sOptions = extractReaderOptions pstate
                  , sMacros  = extractMacros pstate }
  res <- runParserT rawinline lstate "source" toks
  case res of
       Left _ -> mzero
       Right (il, raw, s) -> do
         updateState $ updateMacros (const $ sMacros s)
         takeP (T.length (untokenize raw))
         return il

tokenize :: Text -> [Tok]
tokenize = totoks (1, 1)

totoks :: (Line, Column) -> Text -> [Tok]
totoks (lin,col) t =
  case T.uncons t of
       Nothing        -> []
       Just (c, rest)
         | c == '\n' ->
           Tok (lin, col) Newline "\n"
           : totoks (lin + 1,1) rest
         | isSpaceOrTab c ->
           let (sps, rest') = T.span isSpaceOrTab t
           in  Tok (lin, col) Spaces sps
               : totoks (lin, col + T.length sps) rest'
         | isAlphaNum c ->
           let (ws, rest') = T.span isAlphaNum t
           in  Tok (lin, col) Word ws
               : totoks (lin, col + T.length ws) rest'
         | c == '%' ->
           let (cs, rest') = T.break (== '\n') rest
           in  Tok (lin, col) Comment ("%" <> cs)
               : totoks (lin, col + 1 + T.length cs) rest'
         | c == '\\' ->
           let isLetterOrAt = (\c' -> isLetter c' || c' == '@')
           in  case T.uncons rest of
                Nothing -> [Tok (lin, col) Symbol (T.singleton c)]
                Just (d, rest')
                  | isLetterOrAt d ->
                      let (ws, rest'') = T.span isLetterOrAt rest
                          (ss, rest''') = T.span isSpaceOrTab rest''
                      in  Tok (lin, col) (CtrlSeq ws) ("\\" <> ws <> ss)
                          : totoks (lin,
                                 col + 1 + T.length ws + T.length ss) rest'''
                  | d == '\t' || d == '\n' -> totoks (lin, col + 1) rest
                  | otherwise  ->
                      Tok (lin, col) (CtrlSeq (T.singleton d)) (T.pack [c,d])
                      : totoks (lin, col + 2) rest'
         | c == '#' ->
           let (t1, t2) = T.span (\d -> d >= '0' && d <= '9') rest
           in  case safeRead (T.unpack t1) of
                    Just i ->
                       Tok (lin, col) (Arg i) ("#" <> t1)
                       : totoks (lin, col + 1 + T.length t1) t2
                    Nothing ->
                       Tok (lin, col) Symbol ("#")
                       : totoks (lin, col + 1) t2
         | c == '^' ->
           case T.uncons rest of
                Just ('^', rest') ->
                  case T.uncons rest' of
                       Just (d, rest'')
                         | isLowerHex d ->
                           case T.uncons rest'' of
                                Just (e, rest''') | isLowerHex e ->
                                  Tok (lin, col) Esc2 (T.pack ['^','^',d,e])
                                  : totoks (lin, col + 4) rest'''
                                _ ->
                                  Tok (lin, col) Esc1 (T.pack ['^','^',d])
                                  : totoks (lin, col + 3) rest''
                         | d < '\128' ->
                                  Tok (lin, col) Esc1 (T.pack ['^','^',d])
                                  : totoks (lin, col + 3) rest''
                       _ -> [Tok (lin, col) Symbol ("^"),
                             Tok (lin, col + 1) Symbol ("^")]
                _ -> Tok (lin, col) Symbol ("^")
                     : totoks (lin, col + 1) rest
         | c == '$' ->
           case T.uncons rest of
                Nothing -> [Tok (lin, col) Symbol "$"]
                Just (d, rest')
                  | d == '$' ->
                      Tok (lin, col) Word "$$"
                      : totoks (lin, col + 2) rest'
                  | otherwise  ->
                      Tok (lin, col) Symbol "$"
                      : totoks (lin, col + 1) rest
         | otherwise ->
           Tok (lin, col) Symbol (T.singleton c) : totoks (lin, col + 1) rest

  where isSpaceOrTab ' '    = True
        isSpaceOrTab '\t'   = True
        isSpaceOrTab '\xa0' = True
        isSpaceOrTab _      = False

isLowerHex :: Char -> Bool
isLowerHex x = x >= '0' && x <= '9' || x >= 'a' && x <= 'f'

untokenize :: [Tok] -> Text
untokenize = mconcat . map untoken

untoken :: Tok -> Text
untoken (Tok _ _ t) = t

satisfyTok :: PandocMonad m => (Tok -> Bool) -> LP m Tok
satisfyTok f =
  try $ do
    res <- tokenPrim (T.unpack . untoken) updatePos matcher
    doMacros 0 -- apply macros on remaining input stream
    return res
  where matcher t | f t       = Just t
                  | otherwise = Nothing
        updatePos :: SourcePos -> Tok -> [Tok] -> SourcePos
        updatePos spos _ (Tok (lin,col) _ _ : _) =
          setSourceColumn (setSourceLine spos lin) col
        updatePos spos _ [] = spos

doMacros :: PandocMonad m => Int -> LP m ()
doMacros n = do
  verbatimMode <- sVerbatimMode <$> getState
  when (not verbatimMode) $ do
    inp <- getInput
    case inp of
         Tok spos (CtrlSeq "begin") _ : Tok _ Symbol "{" :
          Tok _ Word name : Tok _ Symbol "}" : ts
            -> handleMacros spos name ts
         Tok spos (CtrlSeq "end") _ : Tok _ Symbol "{" :
          Tok _ Word name : Tok _ Symbol "}" : ts
            -> handleMacros spos ("end" <> name) ts
         Tok spos (CtrlSeq name) _ : ts
            -> handleMacros spos name ts
         _ -> return ()
  where handleMacros spos name ts = do
                macros <- sMacros <$> getState
                case M.lookup name macros of
                     Nothing -> return ()
                     Just (NewCommandMacro numargs optarg newtoks) -> do
                       setInput ts
                       let getarg = spaces >> bracedOrSingleTok
                       args <- case optarg of
                                    Nothing -> count numargs getarg
                                    Just o  ->
                                       (:) <$> option o bracketedToks
                                           <*> count (numargs - 1) getarg
                       let addTok (Tok _ (Arg i) _) acc | i > 0
                                                        , i <= numargs =
                                 map (setpos spos) (args !! (i - 1)) ++ acc
                           addTok t acc = setpos spos t : acc
                       ts' <- getInput
                       setInput $ foldr addTok ts' newtoks
                       if n > 20  -- detect macro expansion loops
                          then throwError $ PandocMacroLoop (T.unpack name)
                          else doMacros (n + 1)
                     Just (DefMacro macroArgs newtoks) -> do
                       setInput ts
                       let makeParser = \x -> spaces *> makeDefMacroParser x
                       let parsers = map makeParser macroArgs
                       let numargs = length parsers
                       args <- sequence parsers
                       let addTok (Tok _ (Arg i) _) acc | i > 0
                                                        , i <= numargs =
                                 map (setpos spos) (args !! (i - 1)) ++ acc
                           addTok t acc = setpos spos t : acc
                       ts' <- getInput
                       setInput $ foldr addTok ts' newtoks
                       if n > 20  -- detect macro expansion loops
                          then throwError $ PandocMacroLoop (T.unpack name)
                          else doMacros (n + 1)

makeDefMacroParser :: PandocMonad m => DefMacroArg -> LP m [Tok]
makeDefMacroParser NakedDefMacroArg = do
  let end = sp <|> (() <$ symbol '[') <|> (() <$ symbol '{')
  braced <|> (manyTill anyTok $ lookAhead end)
makeDefMacroParser BracedDefMacroArg = braced
makeDefMacroParser BracketedDefMacroArg = bracketed
makeDefMacroParser (SymbolSuffixedDefMacroArg c) = braced <* symbol c
makeDefMacroParser (CtrlSeqSuffixedDefMacroArg name) = manyTill anyTok (controlSeq name)

setpos :: (Line, Column) -> Tok -> Tok
setpos spos (Tok _ tt txt) = Tok spos tt txt

anyControlSeq :: PandocMonad m => LP m Tok
anyControlSeq = satisfyTok isCtrlSeq
  where isCtrlSeq (Tok _ (CtrlSeq _) _) = True
        isCtrlSeq _                     = False

anySymbol :: PandocMonad m => LP m Tok
anySymbol = satisfyTok isSym
  where isSym (Tok _ Symbol _) = True
        isSym _                = False

anyArg :: PandocMonad m => LP m Tok
anyArg = satisfyTok isArg
  where isArg (Tok _ (Arg _) _) = True
        isArg _                 = False

spaces :: PandocMonad m => LP m ()
spaces = skipMany (satisfyTok (tokTypeIn [Comment, Spaces, Newline]))

spaces1 :: PandocMonad m => LP m ()
spaces1 = skipMany1 (satisfyTok (tokTypeIn [Comment, Spaces, Newline]))

tokTypeIn :: [TokType] -> Tok -> Bool
tokTypeIn toktypes (Tok _ tt _) = tt `elem` toktypes

controlSeq :: PandocMonad m => Text -> LP m Tok
controlSeq name = satisfyTok isNamed
  where isNamed (Tok _ (CtrlSeq n) _) = n == name
        isNamed _ = False

symbol :: PandocMonad m => Char -> LP m Tok
symbol c = satisfyTok isc
  where isc (Tok _ Symbol d) = case T.uncons d of
                                    Just (c',_) -> c == c'
                                    _ -> False
        isc _ = False

anyLetterSymbol :: PandocMonad m => LP m Tok
anyLetterSymbol = satisfyTok isc
  where isc (Tok _ Symbol d) = case T.uncons d of
                                    Just (c, _) -> isLetter c
                                    _ -> False
        isc _ = False

symbolIn :: PandocMonad m => [Char] -> LP m Tok
symbolIn cs = satisfyTok isInCs
  where isInCs (Tok _ Symbol d) = case T.uncons d of
                                       Just (c,_) -> c `elem` cs
                                       _ -> False
        isInCs _ = False

matchWord :: PandocMonad m => String -> LP m Tok
matchWord s = satisfyTok isWord
  where isWord (Tok _ Word s') = T.unpack s' == s
        isWord _ = False

sp :: PandocMonad m => LP m ()
sp = whitespace <|> endline

whitespace :: PandocMonad m => LP m ()
whitespace = () <$ satisfyTok isSpaceTok
  where isSpaceTok (Tok _ Spaces _) = True
        isSpaceTok _ = False

newlineTok :: PandocMonad m => LP m ()
newlineTok = () <$ satisfyTok isNewlineTok

isNewlineTok :: Tok -> Bool
isNewlineTok (Tok _ Newline _) = True
isNewlineTok _ = False

comment :: PandocMonad m => LP m ()
comment = () <$ satisfyTok isCommentTok
  where isCommentTok (Tok _ Comment _) = True
        isCommentTok _ = False

anyTok :: PandocMonad m => LP m Tok
anyTok = satisfyTok (const True)

endline :: PandocMonad m => LP m ()
endline = try $ do
  newlineTok
  lookAhead anyTok
  notFollowedBy blankline

blankline :: PandocMonad m => LP m ()
blankline = try $ skipMany whitespace *> newlineTok

primEscape :: PandocMonad m => LP m Char
primEscape = do
  Tok _ toktype t <- satisfyTok (tokTypeIn [Esc1, Esc2])
  case toktype of
       Esc1 -> case T.uncons (T.drop 2 t) of
                    Just (c, _)
                      | c >= '\64' && c <= '\127' -> return (chr (ord c - 64))
                      | otherwise                 -> return (chr (ord c + 64))
                    Nothing -> fail "Empty content of Esc1"
       Esc2 -> case safeRead ('0':'x':T.unpack (T.drop 2 t)) of
                    Just x -> return (chr x)
                    Nothing -> fail $ "Could not read: " ++ T.unpack t
       _    -> fail "Expected an Esc1 or Esc2 token" -- should not happen

bgroup :: PandocMonad m => LP m Tok
bgroup = try $ do
  skipMany sp
  symbol '{' <|> controlSeq "bgroup" <|> controlSeq "begingroup"

egroup :: PandocMonad m => LP m Tok
egroup = (symbol '}' <|> controlSeq "egroup" <|> controlSeq "endgroup"

         -- forgive missing }  TODO: ugly
         <|> (unexpectedEndOfDocument "}" >> return (Tok (0, 0) Spaces "")))

grouped :: (PandocMonad m,  Monoid a) => LP m a -> LP m a
grouped parser = try $ do
  bgroup
  -- first we check for an inner 'grouped', because
  -- {{a,b}} should be parsed the same as {a,b}
  try (grouped parser <* egroup) <|> (mconcat <$> manyTill parser egroup)

wrapped :: PandocMonad m => LP m Tok -> LP m Tok -> LP m [Tok]
wrapped begin end = begin *> wrapped' 1
  where wrapped' (n :: Int) =
          handleEgroup n <|> handleBgroup n <|> handleOther n
        handleEgroup n = do
          t <- end
          if n == 1
             then return []
             else (t:) <$> wrapped' (n - 1)
        handleBgroup n = do
          t <- begin
          (t:) <$> wrapped' (n + 1)
        handleOther n = do
          t <- anyTok
          (t:) <$> wrapped' n

braced :: PandocMonad m => LP m [Tok]
braced = wrapped bgroup egroup

-- TODO: ugly
bracedDumb :: PandocMonad m => Monoid a => LP m a -> LP m a
bracedDumb parser = try $ do
  symbol '{'
  mconcat <$> manyTill parser (symbol '}')

bracketed :: PandocMonad m => LP m [Tok]
bracketed = wrapped (symbol '[') (symbol ']')

bracketedDumb :: PandocMonad m => Monoid a => LP m a -> LP m a
bracketedDumb parser = try $ do
  symbol '['
  mconcat <$> manyTill parser (symbol ']')

-- these two functions are ugly
parseToksToBlocks :: PandocMonad m => LP m [Tok] -> LP m Blocks
parseToksToBlocks tokenizer = do
  toks <- tokenizer
  pstate <- getState
  res <- runParserT blocks pstate "parser" toks
  case res of
       Right r -> return r
       Left e -> fail (show e)

dimenarg :: PandocMonad m => LP m Text
dimenarg = try $ do
  ch  <- option False $ True <$ symbol '='
  Tok _ _ s <- satisfyTok isWordTok
  guard $ (T.take 2 (T.reverse s)) `elem`
           ["pt","pc","in","bp","cm","mm","dd","cc","sp"]
  let num = T.take (T.length s - 2) s
  guard $ T.length num > 0
  guard $ T.all isDigit num
  return $ T.pack ['=' | ch] <> s

-- inline elements:

word :: PandocMonad m => LP m Inlines
word = (str . T.unpack . untoken) <$> satisfyTok isWordTok

regularSymbol :: PandocMonad m => LP m Inlines
regularSymbol = (str . T.unpack . untoken) <$> satisfyTok isRegularSymbol
  where isRegularSymbol (Tok _ Symbol t) = not $ T.any isSpecial t
        isRegularSymbol _ = False
        isSpecial c = c `Set.member` specialChars

specialChars :: Set.Set Char
specialChars = Set.fromList "#$%&~_^\\{}"

isWordTok :: Tok -> Bool
isWordTok (Tok _ Word _) = True
isWordTok _ = False

inlineGroup :: PandocMonad m => LP m Inlines
inlineGroup = do
  ils <- grouped inline
  if isNull ils
     then return mempty
     else return $ spanWith nullAttr ils
          -- we need the span so we can detitlecase bibtex entries;
          -- we need to know when something is {C}apitalized

doLHSverb :: PandocMonad m => LP m Inlines
doLHSverb =
  (codeWith ("",["haskell"],[]) . T.unpack . untokenize)
    <$> manyTill (satisfyTok (not . isNewlineTok)) (symbol '|')

mkImage :: PandocMonad m => [(String, String)] -> String -> LP m Inlines
mkImage options src = do
   let replaceTextwidth (k,v) =
         case numUnit v of
              Just (num, "\\textwidth") -> (k, showFl (num * 100) ++ "%")
              _ -> (k, v)
   let kvs = map replaceTextwidth
             $ filter (\(k,_) -> k `elem` ["width", "height"]) options
   let attr = ("",[], kvs)
   let alt = str "image"
   case takeExtension src of
        "" -> do
              defaultExt <- getOption readerDefaultImageExtension
              return $ imageWith attr (addExtension src defaultExt) "" alt
        _  -> return $ imageWith attr src "" alt

doxspace :: PandocMonad m => LP m Inlines
doxspace = do
  (space <$ lookAhead (satisfyTok startsWithLetter)) <|> return mempty
  where startsWithLetter (Tok _ Word t) =
          case T.uncons t of
               Just (c, _) | isLetter c -> True
               _ -> False
        startsWithLetter _ = False


-- converts e.g. \SI{1}[\$]{} to "$ 1" or \SI{1}{\euro} to "1 €"
dosiunitx :: PandocMonad m => LP m Inlines
dosiunitx = do
  skipopts
  value <- tok
  valueprefix <- option "" $ bracketedDumb tok
  unit <- option "" $ bracedDumb tok
  let emptyOr160 "" = ""
      emptyOr160 _  = " "
  return . mconcat $ [valueprefix,
                      emptyOr160 valueprefix,
                      value,
                      emptyOr160 unit,
                      unit]

lit :: String -> LP m Inlines
lit = pure . str

removeDoubleQuotes :: Text -> Text
removeDoubleQuotes t =
  maybe t id $ T.stripPrefix "\"" t >>= T.stripSuffix "\""

doubleQuote :: PandocMonad m => LP m Inlines
doubleQuote = do
       quoted' doubleQuoted (try $ count 2 $ symbol '`')
                            (void $ try $ count 2 $ symbol '\'')
   <|> quoted' doubleQuoted ((:[]) <$> symbol '“') (void $ symbol '”')
   -- the following is used by babel for localized quotes:
   <|> quoted' doubleQuoted (try $ sequence [symbol '"', symbol '`'])
                            (void $ try $ sequence [symbol '"', symbol '\''])
   <|> quoted' doubleQuoted ((:[]) <$> symbol '"')
                            (void $ symbol '"')

singleQuote :: PandocMonad m => LP m Inlines
singleQuote = do
       quoted' singleQuoted ((:[]) <$> symbol '`')
                            (try $ symbol '\'' >>
                                  notFollowedBy (satisfyTok startsWithLetter))
   <|> quoted' singleQuoted ((:[]) <$> symbol '‘')
                            (try $ symbol '’' >>
                                  notFollowedBy (satisfyTok startsWithLetter))
  where startsWithLetter (Tok _ Word t) =
          case T.uncons t of
               Just (c, _) | isLetter c -> True
               _ -> False
        startsWithLetter _ = False

quoted' :: PandocMonad m
        => (Inlines -> Inlines)
        -> LP m [Tok]
        -> LP m ()
        -> LP m Inlines
quoted' f starter ender = do
  startchs <- (T.unpack . untokenize) <$> starter
  smart <- extensionEnabled Ext_smart <$> getOption readerExtensions
  if smart
     then do
       ils <- many (notFollowedBy ender >> inline)
       (ender >> return (f (mconcat ils))) <|>
            (<> mconcat ils) <$>
                    lit (case startchs of
                              "``" -> "“"
                              "`"  -> "‘"
                              cs   -> cs)
     else lit startchs

enquote :: PandocMonad m => LP m Inlines
enquote = do
  skipopts
  quoteContext <- sQuoteContext <$> getState
  if quoteContext == InDoubleQuote
     then singleQuoted <$> withQuoteContext InSingleQuote tok
     else doubleQuoted <$> withQuoteContext InDoubleQuote tok

doverb :: PandocMonad m => LP m Inlines
doverb = do
  Tok _ Symbol t <- anySymbol
  marker <- case T.uncons t of
              Just (c, ts) | T.null ts -> return c
              _ -> mzero
  withVerbatimMode $
    (code . T.unpack . untokenize) <$>
      manyTill (verbTok marker) (symbol marker)

verbTok :: PandocMonad m => Char -> LP m Tok
verbTok stopchar = do
  t@(Tok (lin, col) toktype txt) <- satisfyTok (not . isNewlineTok)
  case T.findIndex (== stopchar) txt of
       Nothing -> return t
       Just i  -> do
         let (t1, t2) = T.splitAt i txt
         inp <- getInput
         setInput $ Tok (lin, col + i) Symbol (T.singleton stopchar)
                  : (totoks (lin, col + i + 1) (T.drop 1 t2)) ++ inp
         return $ Tok (lin, col) toktype t1

dolstinline :: PandocMonad m => LP m Inlines
dolstinline = do
  options <- option [] keyvals
  let classes = maybeToList $ lookup "language" options >>= fromListingsLanguage
  Tok _ Symbol t <- anySymbol
  marker <- case T.uncons t of
              Just (c, ts) | T.null ts -> return c
              _ -> mzero
  let stopchar = if marker == '{' then '}' else marker
  withVerbatimMode $
    (codeWith ("",classes,[]) . T.unpack . untokenize) <$>
      manyTill (verbTok stopchar) (symbol stopchar)

keyval :: PandocMonad m => LP m (String, String)
keyval = try $ do
  Tok _ Word key <- satisfyTok isWordTok
  let isSpecSym (Tok _ Symbol t) = t `elem` [".",":","-","|","\\"]
      isSpecSym _ = False
  val <- option [] $ do
           symbol '='
           braced <|> (many1 (satisfyTok isWordTok <|> satisfyTok isSpecSym
                               <|> anyControlSeq))
  optional sp
  optional (symbol ',')
  optional sp
  return (T.unpack key, T.unpack . untokenize $ val)

keyvals :: PandocMonad m => LP m [(String, String)]
keyvals = try $ symbol '[' >> manyTill keyval (symbol ']')

accent :: (Char -> String) -> Inlines -> LP m Inlines
accent f ils =
  case toList ils of
       (Str (x:xs) : ys) -> return $ fromList (Str (f x ++ xs) : ys)
       []                -> mzero
       _                 -> return ils

grave :: Char -> String
grave 'A' = "À"
grave 'E' = "È"
grave 'I' = "Ì"
grave 'O' = "Ò"
grave 'U' = "Ù"
grave 'a' = "à"
grave 'e' = "è"
grave 'i' = "ì"
grave 'o' = "ò"
grave 'u' = "ù"
grave c   = [c]

acute :: Char -> String
acute 'A' = "Á"
acute 'E' = "É"
acute 'I' = "Í"
acute 'O' = "Ó"
acute 'U' = "Ú"
acute 'Y' = "Ý"
acute 'a' = "á"
acute 'e' = "é"
acute 'i' = "í"
acute 'o' = "ó"
acute 'u' = "ú"
acute 'y' = "ý"
acute 'C' = "Ć"
acute 'c' = "ć"
acute 'L' = "Ĺ"
acute 'l' = "ĺ"
acute 'N' = "Ń"
acute 'n' = "ń"
acute 'R' = "Ŕ"
acute 'r' = "ŕ"
acute 'S' = "Ś"
acute 's' = "ś"
acute 'Z' = "Ź"
acute 'z' = "ź"
acute c   = [c]

circ :: Char -> String
circ 'A' = "Â"
circ 'E' = "Ê"
circ 'I' = "Î"
circ 'O' = "Ô"
circ 'U' = "Û"
circ 'a' = "â"
circ 'e' = "ê"
circ 'i' = "î"
circ 'o' = "ô"
circ 'u' = "û"
circ 'C' = "Ĉ"
circ 'c' = "ĉ"
circ 'G' = "Ĝ"
circ 'g' = "ĝ"
circ 'H' = "Ĥ"
circ 'h' = "ĥ"
circ 'J' = "Ĵ"
circ 'j' = "ĵ"
circ 'S' = "Ŝ"
circ 's' = "ŝ"
circ 'W' = "Ŵ"
circ 'w' = "ŵ"
circ 'Y' = "Ŷ"
circ 'y' = "ŷ"
circ c   = [c]

tilde :: Char -> String
tilde 'A' = "Ã"
tilde 'a' = "ã"
tilde 'O' = "Õ"
tilde 'o' = "õ"
tilde 'I' = "Ĩ"
tilde 'i' = "ĩ"
tilde 'U' = "Ũ"
tilde 'u' = "ũ"
tilde 'N' = "Ñ"
tilde 'n' = "ñ"
tilde c   = [c]

umlaut :: Char -> String
umlaut 'A' = "Ä"
umlaut 'E' = "Ë"
umlaut 'I' = "Ï"
umlaut 'O' = "Ö"
umlaut 'U' = "Ü"
umlaut 'a' = "ä"
umlaut 'e' = "ë"
umlaut 'i' = "ï"
umlaut 'o' = "ö"
umlaut 'u' = "ü"
umlaut c   = [c]

hungarumlaut :: Char -> String
hungarumlaut 'A' = "A̋"
hungarumlaut 'E' = "E̋"
hungarumlaut 'I' = "I̋"
hungarumlaut 'O' = "Ő"
hungarumlaut 'U' = "Ű"
hungarumlaut 'Y' = "ӳ"
hungarumlaut 'a' = "a̋"
hungarumlaut 'e' = "e̋"
hungarumlaut 'i' = "i̋"
hungarumlaut 'o' = "ő"
hungarumlaut 'u' = "ű"
hungarumlaut 'y' = "ӳ"
hungarumlaut c   = [c]

dot :: Char -> String
dot 'C' = "Ċ"
dot 'c' = "ċ"
dot 'E' = "Ė"
dot 'e' = "ė"
dot 'G' = "Ġ"
dot 'g' = "ġ"
dot 'I' = "İ"
dot 'Z' = "Ż"
dot 'z' = "ż"
dot c   = [c]

macron :: Char -> String
macron 'A' = "Ā"
macron 'E' = "Ē"
macron 'I' = "Ī"
macron 'O' = "Ō"
macron 'U' = "Ū"
macron 'a' = "ā"
macron 'e' = "ē"
macron 'i' = "ī"
macron 'o' = "ō"
macron 'u' = "ū"
macron c   = [c]

cedilla :: Char -> String
cedilla 'c' = "ç"
cedilla 'C' = "Ç"
cedilla 's' = "ş"
cedilla 'S' = "Ş"
cedilla 't' = "ţ"
cedilla 'T' = "Ţ"
cedilla 'e' = "ȩ"
cedilla 'E' = "Ȩ"
cedilla 'h' = "ḩ"
cedilla 'H' = "Ḩ"
cedilla 'o' = "o̧"
cedilla 'O' = "O̧"
cedilla c   = [c]

hacek :: Char -> String
hacek 'A' = "Ǎ"
hacek 'a' = "ǎ"
hacek 'C' = "Č"
hacek 'c' = "č"
hacek 'D' = "Ď"
hacek 'd' = "ď"
hacek 'E' = "Ě"
hacek 'e' = "ě"
hacek 'G' = "Ǧ"
hacek 'g' = "ǧ"
hacek 'H' = "Ȟ"
hacek 'h' = "ȟ"
hacek 'I' = "Ǐ"
hacek 'i' = "ǐ"
hacek 'j' = "ǰ"
hacek 'K' = "Ǩ"
hacek 'k' = "ǩ"
hacek 'L' = "Ľ"
hacek 'l' = "ľ"
hacek 'N' = "Ň"
hacek 'n' = "ň"
hacek 'O' = "Ǒ"
hacek 'o' = "ǒ"
hacek 'R' = "Ř"
hacek 'r' = "ř"
hacek 'S' = "Š"
hacek 's' = "š"
hacek 'T' = "Ť"
hacek 't' = "ť"
hacek 'U' = "Ǔ"
hacek 'u' = "ǔ"
hacek 'Z' = "Ž"
hacek 'z' = "ž"
hacek c   = [c]

breve :: Char -> String
breve 'A' = "Ă"
breve 'a' = "ă"
breve 'E' = "Ĕ"
breve 'e' = "ĕ"
breve 'G' = "Ğ"
breve 'g' = "ğ"
breve 'I' = "Ĭ"
breve 'i' = "ĭ"
breve 'O' = "Ŏ"
breve 'o' = "ŏ"
breve 'U' = "Ŭ"
breve 'u' = "ŭ"
breve c   = [c]

toksToString :: [Tok] -> String
toksToString = T.unpack . untokenize

mathDisplay :: String -> Inlines
mathDisplay = displayMath . trim

mathInline :: String -> Inlines
mathInline = math . trim

dollarsMath :: PandocMonad m => LP m Inlines
dollarsMath = do
  symbol '$'
  contents <- trim . toksToString <$>
              many (notFollowedBy (symbol '$') >> anyTok)
  mathInline contents <$ (symbol '$')

doubleDollarsMath :: PandocMonad m => LP m Inlines
doubleDollarsMath = do
  matchWord "$$"
  contents <- trim . toksToString <$>
              many (notFollowedBy (matchWord "$$") >> anyTok)
  mathDisplay contents <$ try (matchWord "$$")
        <|> (guard (null contents) >> return (mathInline ""))

-- citations

addPrefix :: [Inline] -> [Citation] -> [Citation]
addPrefix p (k:ks) = k {citationPrefix = p ++ citationPrefix k} : ks
addPrefix _ _      = []

addSuffix :: [Inline] -> [Citation] -> [Citation]
addSuffix s ks@(_:_) =
  let k = last ks
  in  init ks ++ [k {citationSuffix = citationSuffix k ++ s}]
addSuffix _ _ = []

simpleCiteArgs :: PandocMonad m => LP m [Citation]
simpleCiteArgs = try $ do
  first  <- optionMaybe $ toList <$> opt
  second <- optionMaybe $ toList <$> opt
  labels <- untokenize <$> braced
  let keys = map T.unpack (T.splitOn (T.pack ",") labels)  --TODO: ugly
  let (pre, suf) = case (first  , second ) of
        (Just s , Nothing) -> (mempty, s )
        (Just s , Just t ) -> (s , t )
        _                  -> (mempty, mempty)
      conv k = Citation { citationId      = k
                        , citationPrefix  = []
                        , citationSuffix  = []
                        , citationMode    = NormalCitation
                        , citationHash    = 0
                        , citationNoteNum = 0
                        }
  return $ addPrefix pre $ addSuffix suf $ map conv keys

cites :: PandocMonad m => CitationMode -> Bool -> LP m [Citation]
cites mode multi = try $ do
  cits <- if multi
             then many1 simpleCiteArgs
             else count 1 simpleCiteArgs
  let cs = concat cits
  return $ case mode of
        AuthorInText -> case cs of
                             (c:rest) -> c {citationMode = mode} : rest
                             []       -> []
        _            -> map (\a -> a {citationMode = mode}) cs

citation :: PandocMonad m => String -> CitationMode -> Bool -> LP m Inlines
citation name mode multi = do
  (c,raw) <- withRaw $ cites mode multi
  return $ cite c (rawInline "latex" $ "\\" ++ name ++ (toksToString raw))

handleCitationPart :: Inlines -> [Citation]
handleCitationPart ils =
  let isCite Cite{} = True
      isCite _      = False
      (pref, rest) = break isCite (toList ils)
  in case rest of
          (Cite cs _:suff) -> addPrefix pref $ addSuffix suff cs
          _                -> []

complexNatbibCitation :: PandocMonad m => CitationMode -> LP m Inlines
complexNatbibCitation mode = try $ do
  (cs, raw) <-
    withRaw $ concat <$> do
      bgroup
      items <- mconcat <$>
                many1 (notFollowedBy (symbol ';') >> inline)
                  `sepBy1` (symbol ';')
      egroup
      return $ map handleCitationPart items
  case cs of
       []       -> mzero
       (c:cits) -> return $ cite (c{ citationMode = mode }:cits)
                      (rawInline "latex" $ "\\citetext" ++ toksToString raw)

inNote :: Inlines -> Inlines
inNote ils =
  note $ para $ ils <> str "."

inlineCommand' :: PandocMonad m => LP m Inlines
inlineCommand' = try $ do
  Tok _ (CtrlSeq name) cmd <- anyControlSeq
  guard $ name /= "begin" && name /= "end"
  star <- option "" ("*" <$ symbol '*' <* optional sp)
  let name' = name <> star
  let names = ordNub [name', name] -- check non-starred as fallback
  let raw = do
       guard $ isInlineCommand name || not (isBlockCommand name)
       rawcommand <- getRawCommand (cmd <> star)
       (guardEnabled Ext_raw_tex >> return (rawInline "latex" rawcommand))
         <|> ignore rawcommand
  lookupListDefault raw names inlineCommands

inlineCommandOuterBraced :: PandocMonad m => LP m Inlines
inlineCommandOuterBraced = try $ do
  bgroup
  c <- command
  egroup
  return c
  where command = cmd "em" emph
                  <|> cmd "it" emph
                  <|> cmd "sl" emph
                  <|> cmd "bf" strong
                  <|> cmd "boldmath" strong
                  <|> cmd "rm" id
                  <|> cmd "sc" smallcaps
                  <|> cmd "tt" typewriter
                  <|> cmd "small" id
                  <|> (controlSeq "color" >> coloredInline "color")
        cmd = (\s -> \f -> controlSeq s >> extractSpaces f <$> inlines)

tok :: PandocMonad m => LP m Inlines
tok = grouped inline <|> inlineCommand' <|> inline

opt :: PandocMonad m => LP m Inlines
opt = bracketedDumb inline

rawopt :: PandocMonad m => LP m Text
rawopt = do
  symbol '['
  inner <- untokenize <$> manyTill anyTok (symbol ']')
  optional comment
  optional sp
  return $ "[" <> inner <> "]"

skipopts :: PandocMonad m => LP m ()
skipopts = skipMany rawopt

-- opts in angle brackets are used in beamer
rawangle :: PandocMonad m => LP m ()
rawangle = try $ do
  symbol '<'
  () <$ manyTill anyTok (symbol '>')

skipangles :: PandocMonad m => LP m ()
skipangles = skipMany rawangle

ignore :: (Monoid a, PandocMonad m) => String -> ParserT s u m a
ignore raw = do
  pos <- getPosition
  report $ SkippedContent raw pos
  return mempty

withRaw :: PandocMonad m => LP m a -> LP m (a, [Tok])
withRaw parser = do
  inp <- getInput
  result <- parser
  nxt <- option (Tok (0,0) Word "") (lookAhead anyTok)
  let raw = takeWhile (/= nxt) inp
  return (result, raw)

inBrackets :: Inlines -> Inlines
inBrackets x = str "[" <> x <> str "]"

unescapeURL :: String -> String
unescapeURL ('\\':x:xs) | isEscapable x = x:unescapeURL xs
  where isEscapable c = c `elem` ("#$%&~_^\\{}" :: String)
unescapeURL (x:xs) = x:unescapeURL xs
unescapeURL [] = ""

mathEnvWith :: PandocMonad m
            => (Inlines -> a) -> Maybe Text -> Text -> LP m a
mathEnvWith f innerEnv name = f . mathDisplay . inner <$> mathEnv name
   where inner x = case innerEnv of
                        Nothing -> x
                        Just y  -> "\\begin{" ++ T.unpack y ++ "}\n" ++ x ++
                                   "\\end{" ++ T.unpack y ++ "}"

mathEnv :: PandocMonad m => Text -> LP m String
mathEnv name = do
  skipopts
  optional blankline
  res <- manyTill anyTok (end_ name)
  return $ stripTrailingNewlines $ T.unpack $ untokenize res

inlineEnvironment :: PandocMonad m => LP m Inlines
inlineEnvironment = try $ do
  controlSeq "begin"
  name <- untokenize <$> braced
  M.findWithDefault mzero name inlineEnvironments

inlineEnvironments :: PandocMonad m => M.Map Text (LP m Inlines)
inlineEnvironments = M.fromList [
    ("displaymath", mathEnvWith id Nothing "displaymath")
  , ("math", math <$> mathEnv "math")
  , ("equation", mathEnvWith id Nothing "equation")
  , ("equation*", mathEnvWith id Nothing "equation*")
  , ("gather", mathEnvWith id (Just "gathered") "gather")
  , ("gather*", mathEnvWith id (Just "gathered") "gather*")
  , ("multline", mathEnvWith id (Just "gathered") "multline")
  , ("multline*", mathEnvWith id (Just "gathered") "multline*")
  , ("eqnarray", mathEnvWith id (Just "aligned") "eqnarray")
  , ("eqnarray*", mathEnvWith id (Just "aligned") "eqnarray*")
  , ("align", mathEnvWith id (Just "aligned") "align")
  , ("align*", mathEnvWith id (Just "aligned") "align*")
  , ("alignat", mathEnvWith id (Just "aligned") "alignat")
  , ("alignat*", mathEnvWith id (Just "aligned") "alignat*")
  , ("normalsize", env "normalsize" tok)
  , ("flushleft", env "flushleft" tok)
  ]

inlineCommands :: PandocMonad m => M.Map Text (LP m Inlines)
inlineCommands = M.fromList $
  [ ("emph", extractSpaces emph <$> tok)
  , ("textit", extractSpaces emph <$> tok)
  , ("textsl", extractSpaces emph <$> tok)
  , ("textsc", extractSpaces smallcaps <$> tok)
  , ("textsf", extractSpaces (spanWith ("",["sans-serif"],[])) <$> tok)
  , ("textmd", extractSpaces (spanWith ("",["medium"],[])) <$> tok)
  , ("textrm", extractSpaces (spanWith ("",["roman"],[])) <$> tok)
  , ("small", extractSpaces (spanWith ("",["small"],[])) <$> tok)
  , ("text", tok)
  , ("textup", extractSpaces (spanWith ("",["upright"],[])) <$> tok)
  , ("texttt", ttfamily)
  , ("sout", extractSpaces strikeout <$> tok)
  , ("textsuperscript", extractSpaces superscript <$> tok)
  , ("textsubscript", extractSpaces subscript <$> tok)
  , ("textbackslash", lit "\\")
  , ("backslash", lit "\\")
  , ("slash", lit "/")
  , ("textbf", extractSpaces strong <$> tok)
  , ("textnormal", extractSpaces (spanWith ("",["nodecor"],[])) <$> tok)
  , ("ldots", lit "…")
  , ("vdots", lit "\8942")
  , ("dots", lit "…")
  , ("mdots", lit "…")
  , ("sim", lit "~")
  , ("label", rawInlineOr "label" (inBrackets <$> tok))
  , ("ref", rawInlineOr "ref" (inBrackets <$> tok))
  , ("textgreek", tok)
  , ("sep", lit ",")
  , ("cref", rawInlineOr "cref" (inBrackets <$> tok))  -- from cleveref.sty
  , ("(", mathInline . toksToString <$> manyTill anyTok (controlSeq ")"))
  , ("[", mathDisplay . toksToString <$> manyTill anyTok (controlSeq "]"))
  , ("ensuremath", mathInline . toksToString <$> braced)
  , ("texorpdfstring", (\_ x -> x) <$> tok <*> tok)
  , ("P", lit "¶")
  , ("S", lit "§")
  , ("$", lit "$")
  , ("%", lit "%")
  , ("&", lit "&")
  , ("#", lit "#")
  , ("_", lit "_")
  , ("{", lit "{")
  , ("}", lit "}")
  -- old TeX commands
  , ("em", extractSpaces emph <$> inlines)
  , ("it", extractSpaces emph <$> inlines)
  , ("sl", extractSpaces emph <$> inlines)
  , ("bf", extractSpaces strong <$> inlines)
  , ("sf", extractSpaces (spanWith ("",["sans-serif"],[])) <$> tok)
  , ("sc", extractSpaces smallcaps <$> tok)
  , ("rm", inlines)
  , ("itshape", extractSpaces emph <$> inlines)
  , ("slshape", extractSpaces emph <$> inlines)
  , ("scshape", extractSpaces smallcaps <$> inlines)
  , ("bfseries", extractSpaces strong <$> inlines)
  , ("/", pure mempty) -- italic correction
  , ("aa", lit "å")
  , ("AA", lit "Å")
  , ("ss", lit "ß")
  , ("o", lit "ø")
  , ("O", lit "Ø")
  , ("L", lit "Ł")
  , ("l", lit "ł")
  , ("ae", lit "æ")
  , ("AE", lit "Æ")
  , ("oe", lit "œ")
  , ("OE", lit "Œ")
  , ("pounds", lit "£")
  , ("euro", lit "€")
  , ("copyright", lit "©")
  , ("textasciicircum", lit "^")
  , ("textasciitilde", lit "~")
  , ("H", try $ tok >>= accent hungarumlaut)
  , ("`", option (str "`") $ try $ tok >>= accent grave)
  , ("'", option (str "'") $ try $ tok >>= accent acute)
  , ("^", option (str "^") $ try $ tok >>= accent circ)
  , ("~", option (str "~") $ try $ tok >>= accent tilde)
  , ("\"", option (str "\"") $ try $ tok >>= accent umlaut)
  , (".", option (str ".") $ try $ tok >>= accent dot)
  , ("=", option (str "=") $ try $ tok >>= accent macron)
  , ("c", option (str "c") $ try $ tok >>= accent cedilla)
  , ("v", option (str "v") $ try $ tok >>= accent hacek)
  , ("u", option (str "u") $ try $ tok >>= accent breve)
  , ("i", lit "i")
  , ("\\", linebreak <$ (do inTableCell <- sInTableCell <$> getState
                            guard $ not inTableCell
                            optional (bracketedDumb inline)
                            spaces))
  , (",", lit "\8198")
  , ("@", pure mempty)
  , (" ", lit " ")
  , ("ps", pure $ str "PS." <> space)
  , ("TeX", lit "TeX")
  , ("LaTeX", lit "LaTeX")
  , ("bar", lit "|")
  , ("textless", lit "<")
  , ("textgreater", lit ">")
  , ("thanks", note <$> grouped block)
  , ("footnote", skipopts >> note <$> grouped block)
  , ("verb", doverb)
  , ("lstinline", dolstinline)
  , ("Verb", doverb)
  , ("url", url)
  , ("href", (unescapeURL . toksToString <$>
                 braced <* optional sp) >>= \url ->
                   tok >>= \lab -> pure (link url "" lab))
  , ("includegraphics", do optional $ bracketedDumb inline
                           src <- unescapeURL . T.unpack .
                                    removeDoubleQuotes . untokenize <$> braced
                           mkImage [] src)
  , ("enquote", enquote)
  , ("cite", citation "cite" NormalCitation False)
  , ("Cite", citation "Cite" NormalCitation False)
  , ("citep", citation "citep" NormalCitation False)
  , ("citep*", citation "citep*" NormalCitation False)
  , ("citeal", citation "citeal" NormalCitation False)
  , ("citealp", citation "citealp" NormalCitation False)
  , ("citealp*", citation "citealp*" NormalCitation False)
  , ("autocite", citation "autocite" NormalCitation False)
  , ("smartcite", citation "smartcite" NormalCitation False)
  , ("footcite", inNote <$> citation "footcite" NormalCitation False)
  , ("parencite", citation "parencite" NormalCitation False)
  , ("supercite", citation "supercite" NormalCitation False)
  , ("footcitetext", inNote <$> citation "footcitetext" NormalCitation False)
  , ("citeyearpar", citation "citeyearpar" SuppressAuthor False)
  , ("citeyear", citation "citeyear" SuppressAuthor False)
  , ("autocite*", citation "autocite*" SuppressAuthor False)
  , ("cite*", citation "cite*" SuppressAuthor False)
  , ("parencite*", citation "parencite*" SuppressAuthor False)
  , ("textcite", citation "textcite" AuthorInText False)
  , ("citet", citation "citet" AuthorInText False)
  , ("citet*", citation "citet*" AuthorInText False)
  , ("citealt", citation "citealt" AuthorInText False)
  , ("citealt*", citation "citealt*" AuthorInText False)
  , ("textcites", citation "textcites" AuthorInText True)
  , ("cites", citation "cites" NormalCitation True)
  , ("autocites", citation "autocites" NormalCitation True)
  , ("footcites", inNote <$> citation "footcites" NormalCitation True)
  , ("parencites", citation "parencites" NormalCitation True)
  , ("supercites", citation "supercites" NormalCitation True)
  , ("footcitetexts", inNote <$> citation "footcitetexts" NormalCitation True)
  , ("Autocite", citation "Autocite" NormalCitation False)
  , ("Smartcite", citation "Smartcite" NormalCitation False)
  , ("Footcite", citation "Footcite" NormalCitation False)
  , ("Parencite", citation "Parencite" NormalCitation False)
  , ("Supercite", citation "Supercite" NormalCitation False)
  , ("Footcitetext", inNote <$> citation "Footcitetext" NormalCitation False)
  , ("Citeyearpar", citation "Citeyearpar" SuppressAuthor False)
  , ("Citeyear", citation "Citeyear" SuppressAuthor False)
  , ("Autocite*", citation "Autocite*" SuppressAuthor False)
  , ("Cite*", citation "Cite*" SuppressAuthor False)
  , ("Parencite*", citation "Parencite*" SuppressAuthor False)
  , ("Textcite", citation "Textcite" AuthorInText False)
  , ("Textcites", citation "Textcites" AuthorInText True)
  , ("Cites", citation "Cites" NormalCitation True)
  , ("Autocites", citation "Autocites" NormalCitation True)
  , ("Footcites", citation "Footcites" NormalCitation True)
  , ("Parencites", citation "Parencites" NormalCitation True)
  , ("Supercites", citation "Supercites" NormalCitation True)
  , ("Footcitetexts", inNote <$> citation "Footcitetexts" NormalCitation True)
  , ("citetext", complexNatbibCitation NormalCitation)
  , ("citeauthor", (try (tok *> optional sp *> controlSeq "citetext") *>
                        complexNatbibCitation AuthorInText)
                   <|> citation "citeauthor" AuthorInText False)
  , ("nocite", mempty <$ (citation "nocite" NormalCitation False >>=
                          addMeta "nocite"))
  , ("hypertarget", braced >> tok)
  -- siuntix
  , ("SI", dosiunitx)
  -- hyphenat
  , ("bshyp", lit "\\\173")
  , ("fshyp", lit "/\173")
  , ("dothyp", lit ".\173")
  , ("colonhyp", lit ":\173")
  , ("hyp", lit "-")
  , ("nohyphens", tok)
  , ("textnhtt", ttfamily)
  , ("nhttfamily", ttfamily)
  -- LaTeX colors
  , ("textcolor", coloredInline "color")
  , ("colorbox", coloredInline "background-color")
  -- fontawesome
  , ("faCheck", lit "\10003")
  , ("faClose", lit "\10007")
  -- xspace
  , ("xspace", doxspace)
  -- etoolbox
  , ("ifstrequal", ifstrequal)
  , ("And", lit "and")
  , ("AND", lit "and")
  , ("tt", ttfamily)
  , ("multirow", tok >> tok >>
       ((spanWith ("",["multirow-cell"],[])) <$>  inline))
  , ("thanks", extractSpaces (spanWith ("",["thanks"],[])) <$> inline)
  , ("color", coloredInline "color")
  , ("email", url)

   -- if there is an else block, it's possible it will break environment
   -- balancing. always assume whatever if condition holds.
  , ("else", mempty <$ (manyTill anyTok $ controlSeq "fi"))
  , ("parbox", skipopts >> braced >> tok)

   -- pinforms3 ugghh -- TODO: put these in meta instead
   , ("AUTHOR", spanWith ("", ["author"], []) <$> inline)
   , ("AFF", spanWith ("", ["affiliation"], []) <$> inline)
  ]

ifstrequal :: PandocMonad m => LP m Inlines
ifstrequal = do
  str1 <- tok
  str2 <- tok
  ifequal <- braced
  ifnotequal <- braced
  if str1 == str2
     then getInput >>= setInput . (ifequal ++)
     else getInput >>= setInput . (ifnotequal ++)
  return mempty

coloredInline :: PandocMonad m => String -> LP m Inlines
coloredInline stylename =  do
  skipopts
  color <- braced
  spanWith ("",[],[("style",stylename ++ ": " ++ toksToString color)]) <$> inlines

ttfamily :: PandocMonad m => LP m Inlines
ttfamily = typewriter <$> tok

typewriter :: Inlines -> Inlines
typewriter = code . stringify . toList

url :: PandocMonad m => LP m Inlines
url = do
  u <- (unescapeURL . T.unpack . untokenize) <$> braced
  return $ link u "" (str u)

rawInlineOr :: PandocMonad m => Text -> LP m Inlines -> LP m Inlines
rawInlineOr name' fallback = do
  parseRaw <- extensionEnabled Ext_raw_tex <$> getOption readerExtensions
  if parseRaw
     then rawInline "latex" <$> getRawCommand name'
     else fallback

getRawCommand :: PandocMonad m => Text -> LP m String
getRawCommand txt = do
  (_, rawargs) <- withRaw $
      case txt of
           "\\write" -> do
             void $ satisfyTok isWordTok -- digits
             void braced
           "\\titleformat" -> do
             void braced
             skipopts
             void $ count 4 braced
           _ -> do
             skipangles
             skipopts
             option "" (try (optional sp *> dimenarg))
             void $ many braced
  return $ T.unpack (txt <> untokenize rawargs)

isBlockCommand :: Text -> Bool
isBlockCommand s =
  s `M.member` (blockCommands :: M.Map Text (LP PandocPure Blocks))
  || s `Set.member` treatAsBlock

treatAsBlock :: Set.Set Text
treatAsBlock = Set.fromList
   [ "newcommand", "renewcommand"
   , "newenvironment", "renewenvironment"
   , "providecommand", "provideenvironment"
     -- newcommand, etc. should be parsed by macroDef, but we need this
     -- here so these aren't parsed as inline commands to ignore
   , "special", "pdfannot", "pdfstringdef"
   , "bibliographystyle"
   , "maketitle", "makeindex", "makeglossary"
   , "addcontentsline", "addtocontents", "addtocounter"
      -- \ignore{} is used conventionally in literate haskell for definitions
      -- that are to be processed by the compiler but not printed.
   , "ignore"
   , "hyperdef"
   , "markboth", "markright", "markleft"
   , "hspace", "vspace"
   , "newpage"
   , "clearpage"
   , "pagebreak"
   , "titleformat"
   ]

isInlineCommand :: Text -> Bool
isInlineCommand s =
  s `M.member` (inlineCommands :: M.Map Text (LP PandocPure Inlines))
  || s `Set.member` treatAsInline

treatAsInline :: Set.Set Text
treatAsInline = Set.fromList
  [ "index"
  , "hspace"
  , "vspace"
  , "noindent"
  , "newpage"
  , "clearpage"
  , "pagebreak"
  ]

lookupListDefault :: (Show k, Ord k) => v -> [k] -> M.Map k v -> v
lookupListDefault d = (fromMaybe d .) . lookupList
  where lookupList l m = msum $ map (`M.lookup` m) l

inline :: PandocMonad m => LP m Inlines
inline = (mempty <$ comment)
     <|> (space  <$ whitespace)
     <|> (softbreak <$ endline)
     <|> doubleDollarsMath
     <|> word
     <|> inlineCommand'
     <|> inlineEnvironment
     <|> inlineCommandOuterBraced
     <|> inlineGroup
     <|> (symbol '-' *>
           option (str "-") (symbol '-' *>
             option (str "–") (str "—" <$ symbol '-')))
     <|> doubleQuote
     <|> singleQuote
     <|> (str "”" <$ try (symbol '\'' >> symbol '\''))
     <|> (str "”" <$ symbol '”')
     <|> (str "’" <$ symbol '\'')
     <|> (str "’" <$ symbol '’')
     <|> (str " " <$ symbol '~')
     <|> dollarsMath
     <|> (guardEnabled Ext_literate_haskell *> symbol '|' *> doLHSverb)
     <|> (str . (:[]) <$> primEscape)
     <|> regularSymbol
     <|> (do res <- symbolIn "#^'`\"[]_"
             pos <- getPosition
             let s = T.unpack (untoken res)
             report $ ParsingUnescaped s pos
             return $ str s)

inlines :: PandocMonad m => LP m Inlines
inlines = mconcat <$> many inline

-- block elements:

begin_ :: PandocMonad m => Text -> LP m ()
begin_ t = (try $ do
  controlSeq "begin"
  spaces
  txt <- untokenize <$> braced
  guard (t == txt)) <?> ("\\begin{" ++ T.unpack t ++ "}")

end_ :: PandocMonad m => Text -> LP m ()
end_ t = (try $ do
  controlSeq "end"
  spaces
  txt <- untokenize <$> braced
  guard $ t == txt) <?> ("\\end{" ++ T.unpack t ++ "}")

preamble :: PandocMonad m => LP m Blocks
preamble = mempty <$ many preambleBlock
  where preambleBlock =  spaces1
                     <|> void include
                     <|> void macroDef
                     <|> void blockCommand
                     <|> void braced
                     <|> (notFollowedBy (begin_ "document") >> void anyTok)

paragraph :: PandocMonad m => LP m Blocks
paragraph = do
  x <- trimInlines . mconcat <$> many1 inline
  if x == mempty
     then return mempty
     else return $ para x

include :: PandocMonad m => LP m Blocks
include = do
  (Tok _ (CtrlSeq name) _) <-
                    controlSeq "include" <|> controlSeq "input" <|>
                    controlSeq "subfile" -- <|> controlSeq "usepackage"
  skipMany $ bracketedDumb inline -- skip options
  fs <- (map trim . splitBy (==',') . T.unpack . untokenize) <$> braced
  let fs' = if name == "usepackage"
               then map (maybeAddExtension ".sty") fs
               else map (maybeAddExtension ".tex") fs
  dirs <- (splitBy (==':') . fromMaybe ".") <$> lookupEnv "TEXINPUTS"
  mconcat <$> mapM (insertIncludedFile blocks (tokenize . T.pack) dirs) fs'

maybeAddExtension :: String -> FilePath -> FilePath
maybeAddExtension ext fp =
  if null (takeExtension fp)
     then addExtension fp ext
     else fp

addMeta :: PandocMonad m => ToMetaValue a => String -> a -> LP m ()
addMeta field val = updateState $ \st ->
   st{ sMeta = addMetaField field val $ sMeta st }

updateMeta :: PandocMonad m => ToMetaValue a => String -> a -> LP m ()
updateMeta field val = updateState $ \st ->
   st{ sMeta = updateMetaField field val $ sMeta st }
   where updateMetaField key val' (Meta meta) =
           Meta $ M.insert key (MetaList [toMetaValue val']) meta

authors :: PandocMonad m => LP m ()
authors = try $ do
  bgroup
  auths <- sepBy oneAuthor (controlSeq "and")
  egroup
  addMeta "author" (map trimInlines auths)

oneAuthor :: PandocMonad m => LP m Inlines
oneAuthor = do
  name <- mconcat <$> nameParts
  affils <- parseAffils <$> optional (controlSeq "inst" >> braced)
  spaces
  let kvs = map (\a -> ("affiliation-abbrev", T.unpack a)) affils
  return $ spanWith ("", [], kvs) name
  where nameParts = many1
          (notFollowedBy' (controlSeq "and" <|> controlSeq "inst") >>
               authorInline)
               -- skip e.g. \vspace{10pt}
        parseAffils optToks =
          case optToks of
               Just toks' -> T.splitOn "," $ untokenize toks'
               Nothing -> []

authorInline :: PandocMonad m => LP m Inlines
authorInline = inline
               <|> mempty <$ blockCommand
               <|> (str "\n" <$ many1 newlineTok)

institute :: PandocMonad m => LP m ()
institute = do
  bgroup
  names <- sepBy oneInstitute (controlSeq "and")
  egroup
  let namesWithIndices = reverse $ zip [0 :: Int ..] names -- TODO(andreas): why reverse?
  currentAuthors <- authorsInState <$> getState
  let newAuthors = foldr addInstitute currentAuthors namesWithIndices
  updateMeta "author" newAuthors
  where addInstitute (index, name) auths =
          addAffiliation auths (show $ index + 1) name
        oneInstitute = mconcat <$> many1 (
          notFollowedBy' (controlSeq "and") >> authorInline)

authorsInState :: LaTeXState -> Inlines
authorsInState st =
  case lookupMeta "author" (sMeta st) of
         Just (MetaList mils) -> fromList $ concat $ map extractInlines mils
         _ -> fromList []
  where extractInlines (MetaInlines ils) = ils
        extractInlines _ = []

icmlaffiliation :: PandocMonad m => LP m ()
icmlaffiliation = do
  abbrev <- T.unpack <$> untokenize <$> braced
  name <- tok
  st <- getState
  let auths = addAffiliation (authorsInState st) abbrev name
  updateMeta "author" auths

-- TODO(andreas): use walkM instead
addAffiliation :: Inlines -> String -> Inlines -> Inlines
addAffiliation auths abbrev name =
  fromList newAuthList <> affil
  where auths' = toList auths
        numAffils = length $ filter (hasClass "affiliation") auths'
        superNumber = Superscript $ toList $ text $ show $ 1 + numAffils
        affilList = [superNumber] ++ toList name -- TODO nicer
        affil = spanWith ("", ["affiliation"], []) $ fromList affilList
        newAuthList = map updateAffils auths'
        updateAffils (Span (id', classes, kvs) txt) | ("affiliation-abbrev", abbrev) `elem` kvs = Span (id', classes, kvs) $ txt ++ [superNumber] -- TODO nicer
        updateAffils x = x

hasClass :: String -> Inline -> Bool
hasClass cls (Span (_, classes, _) _) = cls `elem` classes
hasClass _ _ = False

icmlauthorlist :: PandocMonad m => LP m ()
icmlauthorlist = do
  auths <- many icmlauthor
  addMeta "author" auths

icmlauthor :: PandocMonad m => LP m Inlines
icmlauthor = do
    spaces
    controlSeq "icmlauthor"
    name <- tok
    affiliations <- T.splitOn "," <$> untokenize <$> braced
    let kvs = map (\a -> ("affiliation-abbrev", T.unpack a)) affiliations
    let attr = ("", ["author"], kvs)
    spaces
    return $ spanWith attr name

macroDef :: PandocMonad m => LP m Blocks
macroDef = do
  mempty <$ ((commandDef <|> environmentDef <|> defDef) <* doMacros 0)
  where commandDef = do
          (name, macro') <- newcommand
          guardDisabled Ext_latex_macros <|>
           updateState (\s -> s{ sMacros = M.insert name macro' (sMacros s) })
        environmentDef = do
          (name, macro1, macro2) <- newenvironment
          guardDisabled Ext_latex_macros <|>
            do updateState $ \s -> s{ sMacros =
                M.insert name macro1 (sMacros s) }
               updateState $ \s -> s{ sMacros =
                M.insert ("end" <> name) macro2 (sMacros s) }
        defDef = do
          (name, macro') <- defCommand
          guardDisabled Ext_latex_macros <|>
           updateState (\s -> s{ sMacros = M.insert name macro' (sMacros s) })
        -- @\newenvironment{envname}[n-args][default]{begin}{end}@
        -- is equivalent to
        -- @\newcommand{\envname}[n-args][default]{begin}@
        -- @\newcommand{\endenvname}@

bracedOrSingleTok :: PandocMonad m => LP m [Tok]
bracedOrSingleTok = braced <|> (toList <$> singleton <$> anyTok)

newcommand :: PandocMonad m => LP m (Text, Macro)
newcommand = withVerbatimMode $ do
  pos <- getPosition
  Tok _ (CtrlSeq mtype) _ <- controlSeq "newcommand" <|>
                             controlSeq "renewcommand" <|>
                             controlSeq "providecommand"
  optional $ symbol '*'
  let ctrlSeqName = try $ do
        Tok _ (CtrlSeq name) _ <- anyControlSeq <|>
          (symbol '{' *> spaces *> anyControlSeq <* spaces <* symbol '}')
        return name
  name <- ctrlSeqName <|> (untokenize <$> braced)
  spaces
  numargs <- option 0 $ try bracketedNum
  spaces
  optarg <- option Nothing $ Just <$> try bracketedToks
  spaces
  contents <- bracedOrSingleTok
  when (mtype == "newcommand") $ do
    macros <- sMacros <$> getState
    case M.lookup name macros of
         Just _ -> report $ MacroAlreadyDefined (T.unpack name) pos
         Nothing -> return ()
  return (name, NewCommandMacro numargs optarg contents)

newenvironment :: PandocMonad m => LP m (Text, Macro, Macro)
newenvironment = withVerbatimMode $ do
  pos <- getPosition
  Tok _ (CtrlSeq mtype) _ <- controlSeq "newenvironment" <|>
                             controlSeq "renewenvironment" <|>
                             controlSeq "provideenvironment"
  optional $ symbol '*'
  spaces
  name <- untokenize <$> braced
  spaces
  numargs <- option 0 $ try bracketedNum
  spaces
  optarg <- option Nothing $ Just <$> try bracketedToks
  spaces
  startcontents <- braced
  spaces
  endcontents <- (braced <|> pure [])
  when (mtype == "newenvironment") $ do
    macros <- sMacros <$> getState
    case M.lookup name macros of
         Just _ -> report $ MacroAlreadyDefined (T.unpack name) pos
         Nothing -> return ()
  return (name, NewCommandMacro numargs optarg startcontents,
             NewCommandMacro 0 Nothing endcontents)

defCommand :: PandocMonad m => LP m (Text, Macro)
defCommand = try $ withVerbatimMode $ do
  spaces
  controlSeq "def"
  spaces
  Tok _ (CtrlSeq name) _ <- anyControlSeq
  spaces
  args <- many defMacroArg
  spaces
  contents <- bracedOrSingleTok
  return (name, DefMacro args contents)

defMacroArg :: PandocMonad m => LP m DefMacroArg
defMacroArg = controlSeqSuffixedArg
              <|> symbolSuffixedArg
              <|> nakedArg
              <|> bracedArg
              <|> bracketedArg
  where nakedArg     = NakedDefMacroArg <$ anyArg
        bracketedArg = BracketedDefMacroArg <$ bracketed
        bracedArg    = try $ BracedDefMacroArg <$ (bgroup >> anyArg >> egroup)
        controlSeqSuffixedArg = try $ do
          anyArg
          spaces
          Tok _ (CtrlSeq name) _ <- anyControlSeq
          return $ CtrlSeqSuffixedDefMacroArg name
        symbolSuffixedArg = try $ do
          anyArg
          (Tok _ Symbol t) <- anySymbol
          case T.uncons t of
               Just (c, _) | not (c `elem` ("{[" :: String)) ->
                                return $ SymbolSuffixedDefMacroArg c
                           | otherwise -> fail "Bad def suffix"
               Nothing -> fail "Empty symbol"

-- TODO: don't ignore (it's hard....)
ignoreNewColumnType :: PandocMonad m => LP m Blocks
ignoreNewColumnType = do
  spaces
  braced
  spaces
  skipopts
  spaces
  (() <$ braced) <|> (() <$ tok)
  return mempty

bracketedToks :: PandocMonad m => LP m [Tok]
bracketedToks = do
  symbol '['
  manyTill anyTok (symbol ']')

bracketedNum :: PandocMonad m => LP m Int
bracketedNum = do
  ds <- untokenize <$> bracketedToks
  case safeRead (T.unpack ds) of
       Just i -> return i
       _      -> return 0

setCaption :: PandocMonad m => LP m Blocks
setCaption = do
  ils <- tok
  mblabel <- option Nothing $
               try $ spaces >> controlSeq "label" >> (Just <$> tok)
  let ils' = case mblabel of
                  Just lab -> ils <> spanWith
                                ("",[],[("data-label", stringify lab)]) mempty
                  Nothing  -> ils
  updateState $ \st -> st{ sCaption = Just ils' }
  return mempty

looseItem :: PandocMonad m => LP m Blocks
looseItem = do
  inListItem <- sInListItem <$> getState
  guard $ not inListItem
  skipopts
  return mempty

resetCaption :: PandocMonad m => LP m ()
resetCaption = updateState $ \st -> st{ sCaption = Nothing }

section :: PandocMonad m => Attr -> Int -> LP m Blocks
section (ident, classes, kvs) lvl = do
  skipopts
  contents <- grouped inline
  lab <- option ident $
          try (spaces >> controlSeq "label"
               >> spaces >> toksToString <$> braced)
  attr' <- registerHeader (lab, classes, kvs) contents
  return $ headerWith attr' lvl contents

blockCommand :: PandocMonad m => LP m Blocks
blockCommand = try $ do
  Tok _ (CtrlSeq name) txt <- anyControlSeq
  guard $ name /= "begin" && name /= "end"
  star <- option "" ("*" <$ symbol '*' <* optional sp)
  let name' = name <> star
  let names = ordNub [name', name]
  let rawDefiniteBlock = do
        guard $ isBlockCommand name
        rawBlock "latex" <$> getRawCommand (txt <> star)
  -- heuristic:  if it could be either block or inline, we
  -- treat it if block if we have a sequence of block
  -- commands followed by a newline.  But we stop if we
  -- hit a \startXXX, since this might start a raw ConTeXt
  -- environment (this is important because this parser is
  -- used by the Markdown reader).
  let startCommand = try $ do
        Tok _ (CtrlSeq n) _ <- anyControlSeq
        guard $ "start" `T.isPrefixOf` n
  let rawMaybeBlock = try $ do
        guard $ not $ isInlineCommand name
        curr <- rawBlock "latex" <$> getRawCommand (txt <> star)
        rest <- many $ notFollowedBy startCommand *> blockCommand
        lookAhead $ blankline <|> startCommand
        return $ curr <> mconcat rest
  let raw = rawDefiniteBlock <|> rawMaybeBlock
  lookupListDefault raw names blockCommands

closing :: PandocMonad m => LP m Blocks
closing = do
  contents <- tok
  st <- getState
  let extractInlines (MetaBlocks [Plain ys]) = ys
      extractInlines (MetaBlocks [Para ys ]) = ys
      extractInlines _                       = []
  let sigs = case lookupMeta "author" (sMeta st) of
                  Just (MetaList xs) ->
                    para $ trimInlines $ fromList $
                      intercalate [LineBreak] $ map extractInlines xs
                  _ -> mempty
  return $ para (trimInlines contents) <> sigs

blockCommands :: PandocMonad m => M.Map Text (LP m Blocks)
blockCommands = M.fromList $
   [ ("par", mempty <$ skipopts)
   , ("parbox",  braced >> grouped blocks)
   , ("title", title)
   , ("subtitle", mempty <$ (skipopts *> tok >>= addMeta "subtitle"))
   , ("author", mempty <$ (skipopts *> authors))
   -- -- in letter class, temp. store address & sig as title, author
   , ("address", mempty <$ (skipopts *> tok >>= addMeta "address"))
   , ("signature", mempty <$ (skipopts *> authors))
   , ("date", mempty <$ (skipopts *> tok >>= addMeta "date"))
   -- Koma-script metadata commands
   , ("dedication", mempty <$ (skipopts *> tok >>= addMeta "dedication"))
   -- sectioning
   , ("part", section nullAttr (-1))
   , ("part*", section nullAttr (-1))
   , ("chapter", section nullAttr 0)
   , ("chapter*", section ("",["unnumbered"],[]) 0)
   , ("section", section nullAttr 1)
   , ("section*", section ("",["unnumbered"],[]) 1)
   , ("subsection", section nullAttr 2)
   , ("subsection*", section ("",["unnumbered"],[]) 2)
   , ("subsubsection", section nullAttr 3)
   , ("subsubsection*", section ("",["unnumbered"],[]) 3)
   , ("paragraph", section nullAttr 4)
   , ("paragraph*", section ("",["unnumbered"],[]) 4)
   , ("subparagraph", section nullAttr 5)
   , ("subparagraph*", section ("",["unnumbered"],[]) 5)
   -- beamer slides
   , ("frametitle", section nullAttr 3)
   , ("framesubtitle", section nullAttr 4)
   -- letters
   , ("opening", (para . trimInlines) <$> (skipopts *> tok))
   , ("closing", skipopts *> closing)
   --
   , ("hrule", pure horizontalRule)
   , ("rule", skipopts *> tok *> tok *> pure horizontalRule)
   , ("item", looseItem)
   , ("documentclass", skipopts *> braced *> preamble)
   , ("centerline", (para . trimInlines) <$> (skipopts *> tok))
   , ("caption", skipopts *> setCaption)
   , ("bibliography", mempty <$ (skipopts *> braced >>=
         addMeta "bibliography" . splitBibs . toksToString))
   , ("addbibresource", mempty <$ (skipopts *> braced >>=
         addMeta "bibliography" . splitBibs . toksToString))
   -- includes
   , ("lstinputlisting", inputListing)
   , ("graphicspath", graphicsPath)
   -- hyperlink
   , ("hypertarget", try $ braced >> grouped block)
   -- LaTeX colors
   , ("textcolor", coloredBlock "color")
   , ("colorbox", coloredBlock "background-color")
   , ("scalebox", braced >> blocks)
   , ("color", coloredBlock "color")
   , ("newcolumntype", ignoreNewColumnType)
   , ("emph", (divWith ("", ["emph"], []) <$> grouped block))  -- TODO: in html!!!
   , ("textbf", (divWith ("", ["textbf"], []) <$> grouped block))  -- TODO: in html!!!
   , ("texttt", (divWith ("", ["texttt"], []) <$> grouped block))  -- TODO: in html!!!
   , ("small", (divWith ("", ["small"], []) <$> grouped block))  -- TODO: in html!!!
   , ("multirow", braced >> braced >>
       ((divWith ("",["multirow-cell"],[])) <$> grouped block))  -- TODO: parses but doesn't actually work!!!
   , ("thanks", (divWith ("",["thanks"],[]) <$> grouped block)) -- TOOD: in html!!!
   , ("else", mempty <$ (manyTill anyTok $ controlSeq "fi"))
   , ("text", blocks)
   , ("bibitem", bibitem)
   , ("newblock", mempty <$ skipopts)
   , ("twocolumn", mempty <$ twocolumn)
   , ("pdfoutput",  try $ mempty <$ (symbol '=' >> tok))
   , ("vskip", mempty <$ (spaces >> manyTill anyTok sp))
   , ("institute", mempty <$ institute)

   -- pinforms3 ugghh
   , ("ABSTRACT", mempty <$ (parseToksToBlocks braced >>= addMeta "abstract"))
   , ("ARTICLEAUTHORS", (divWith ("", ["authors"], []) <$> blocks))
   , ("TITLE", title)

   -- icml
   , ("icmltitle", title)
   , ("icmlaffiliation", mempty <$ icmlaffiliation)
   ]


environments :: PandocMonad m => M.Map Text (LP m Blocks)
environments = M.fromList
   [ ("document", env "document" blocks)
   , ("abstract", mempty <$ (env "abstract" blocks >>= addMeta "abstract"))
   , ("letter", env "letter" letterContents)
   , ("minipage", env "minipage" $
          skipopts *> spaces *> optional braced *> spaces *> blocks)
   , ("figure", env "figure" $ skipopts *> figure)
   , ("figure*", env "figure*" $ skipopts *> figure)
   , ("wrapfigure", env "wrapfigure" $ skipopts *> braced *> skipopts *> braced *> figure)
   , ("subfigure", env "subfigure" $ skipopts *> tok *> figure)
   , ("center", env "center" blocks)
   , ("longtable",  env "longtable" $
          resetCaption *> simpTable "longtable" False >>= addTableCaption)
   , ("table",  env "table" $
          resetCaption *> skipopts *> blocks >>= addTableCaption)
   , ("table*",  env "table*" $
          resetCaption *> skipopts *> blocks >>= addTableCaption)
   , ("tabular*", env "tabular*" $ simpTable "tabular*" True)
   , ("tabularx", env "tabularx" $ simpTable "tabularx" True)
   , ("tabular", env "tabular"  $ simpTable "tabular" False)
   , ("tabu", env "tabu"  $ simpTable "tabu" False)
   , ("tabulary", env "tabulary"  $ simpTable "tabulary" True)
   , ("TAB", env "TAB"  $ easyTable)
   , ("adjustbox", env "adjustbox" adjustbox)
   , ("quote", blockQuote <$> env "quote" blocks)
   , ("quotation", blockQuote <$> env "quotation" blocks)
   , ("verse", blockQuote <$> env "verse" blocks)
   , ("itemize", bulletList <$> listenv "itemize" (many item))
   , ("description", definitionList <$> listenv "description" (many descItem))
   , ("enumerate", orderedList')
   , ("alltt", alltt <$> env "alltt" blocks)
   , ("code", guardEnabled Ext_literate_haskell *>
       (codeBlockWith ("",["sourceCode","literate","haskell"],[]) <$>
         verbEnv "code"))
   , ("comment", mempty <$ verbEnv "comment")
   , ("verbatim", codeBlock <$> verbEnv "verbatim")
   , ("Verbatim", fancyverbEnv "Verbatim")
   , ("BVerbatim", fancyverbEnv "BVerbatim")
   , ("lstlisting", do attr <- parseListingsOptions <$> option [] keyvals
                       codeBlockWith attr <$> verbEnv "lstlisting")
    , ("minted", minted)
   , ("obeylines", obeylines)
   , ("displaymath", mathEnvWith para Nothing "displaymath")
   , ("equation", mathEnvWith para Nothing "equation")
   , ("equation*", mathEnvWith para Nothing "equation*")
   , ("gather", mathEnvWith para (Just "gathered") "gather")
   , ("gather*", mathEnvWith para (Just "gathered") "gather*")
   , ("multline", mathEnvWith para (Just "gathered") "multline")
   , ("multline*", mathEnvWith para (Just "gathered") "multline*")
   , ("eqnarray", mathEnvWith para (Just "aligned") "eqnarray")
   , ("IEEEeqnarray", mathEnvWith para (Just "aligned") "IEEEeqnarray")
   , ("eqnarray*", mathEnvWith para (Just "aligned") "eqnarray*")
   , ("align", mathEnvWith para (Just "aligned") "align")
   , ("align*", mathEnvWith para (Just "aligned") "align*")
   , ("alignat", mathEnvWith para (Just "aligned") "alignat")
   , ("alignat*", mathEnvWith para (Just "aligned") "alignat*")
   , ("empheq", mathEnvWith para (Just "aligned") "empheq")
   , ("flalign", mathEnvWith para (Just "aligned") "flalign")
   , ("flalign*", mathEnvWith para (Just "aligned") "flalign*")
   , ("tikzpicture", rawVerbEnv "tikzpicture")
   , ("algorithm", rawVerbEnv "algorithm")
   , ("small", env "small" blocks)
   -- TODO: handle proof caption "\begin{proof}[Proof of Lemma \ref{lem:graph_path}]" (1707.08238v1)
   , ("proof", env "proof" $ skipopts *> blocks)
   , ("IEEEbiography", env "IEEEbiography" ieeeBiography)
   , ("thebibliography", env "thebibliography" thebibliography)
   , ("figwindow", env "figwindow" figwindow)

   -- icml
   , ("icmlauthorlist", env "icmlauthorlist" (mempty <$ icmlauthorlist))

   -- cjk
   , ("CJK", env "CJK" $ braced *> braced *> blocks)
   , ("CJK*", env "CJK*" $ braced *> braced *> blocks)
   ]

environment :: PandocMonad m => LP m Blocks
environment = do
  controlSeq "begin"
  name <- untokenize <$> braced
  M.findWithDefault mzero name environments
    <|> rawEnv name

env :: PandocMonad m => Text -> LP m a -> LP m a
env name p = p <* endOrEndOfDocument name

rawEnv :: PandocMonad m => Text -> LP m Blocks
rawEnv name = do
  exts <- getOption readerExtensions
  let parseRaw = extensionEnabled Ext_raw_tex exts
  rawOptions <- mconcat <$> many rawopt
  let beginCommand = "\\begin{" <> name <> "}" <> rawOptions
  pos1 <- getPosition
  (bs, raw) <- withRaw $ env name blocks
  if parseRaw
     then return $ rawBlock "latex"
                 $ T.unpack $ beginCommand <> untokenize raw
     else do
       unless parseRaw $ do
         report $ SkippedContent (T.unpack beginCommand) pos1
       pos2 <- getPosition
       report $ SkippedContent ("\\end{" ++ T.unpack name ++ "}") pos2
       return bs

rawVerbEnv :: PandocMonad m => Text -> LP m Blocks
rawVerbEnv name = do
  pos <- getPosition
  (_, raw) <- withRaw $ verbEnv name
  let raw' = "\\begin{" ++ (T.unpack name) ++ "}" ++ toksToString raw
  exts <- getOption readerExtensions
  let parseRaw = extensionEnabled Ext_raw_tex exts
  if parseRaw
     then return $ rawBlock "latex" raw'
     else do
       report $ SkippedContent raw' pos
       return mempty

verbEnv :: PandocMonad m => Text -> LP m String
verbEnv name = withVerbatimMode $ do
  skipopts
  optional blankline
  res <- manyTill anyTok (endOrEndOfDocument name)
  return $ stripTrailingNewlines $ toksToString res

fancyverbEnv :: PandocMonad m => Text -> LP m Blocks
fancyverbEnv name = do
  options <- option [] keyvals
  let kvs = [ (if k == "firstnumber"
                  then "startFrom"
                  else k, v) | (k,v) <- options ]
  let classes = [ "numberLines" |
                  lookup "numbers" options == Just "left" ]
  let attr = ("",classes,kvs)
  codeBlockWith attr <$> verbEnv name

obeylines :: PandocMonad m => LP m Blocks
obeylines = do
  para . fromList . removeLeadingTrailingBreaks .
     walk softBreakToHard . toList <$> env "obeylines" inlines
  where softBreakToHard SoftBreak = LineBreak
        softBreakToHard x         = x
        removeLeadingTrailingBreaks = reverse . dropWhile isLineBreak .
                                      reverse . dropWhile isLineBreak
        isLineBreak LineBreak     = True
        isLineBreak _             = False

title :: PandocMonad m => LP m Blocks
title = mempty <$ (skipopts *>
                       (grouped inline >>= addMeta "title")
                   <|> (grouped block >>= addMeta "title"))

twocolumn :: PandocMonad m => LP m ()
twocolumn = do
  toks <- bracketed
  inp <- getInput
  setInput $ toks ++ inp

ieeeBiography :: PandocMonad m => LP m Blocks
ieeeBiography = do
  options <- option [] $ toList <$> bracketedDumb inline
  name <- toList <$> str <$> toksToString <$> braced
  let ils = fromList (options ++ name)
  let p = para ils
  bs <- blocks
  return $ divWith ("", ["ieeeBiography"], []) $ (p <> bs)

minted :: PandocMonad m => LP m Blocks
minted = do
  options <- option [] keyvals
  lang <- toksToString <$> braced
  let kvs = [ (if k == "firstnumber"
                  then "startFrom"
                  else k, v) | (k,v) <- options ]
  let classes = [ lang | not (null lang) ] ++
                [ "numberLines" |
                  lookup "linenos" options == Just "true" ]
  let attr = ("",classes,kvs)
  codeBlockWith attr <$> verbEnv "minted"

letterContents :: PandocMonad m => LP m Blocks
letterContents = do
  bs <- blocks
  st <- getState
  -- add signature (author) and address (title)
  let addr = case lookupMeta "address" (sMeta st) of
                  Just (MetaBlocks [Plain xs]) ->
                     para $ trimInlines $ fromList xs
                  _ -> mempty
  return $ addr <> bs -- sig added by \closing

figure :: PandocMonad m => LP m Blocks
figure = try $ do
  resetCaption
  blocks >>= addImageCaption >>= addTikzImageCaption

addImageCaption :: PandocMonad m => Blocks -> LP m Blocks
addImageCaption = walkM go
  where go (Image attr alt (src,tit))
            | not ("fig:" `isPrefixOf` tit) = do
          mbcapt <- sCaption <$> getState
          return $ case mbcapt of
               Just ils -> Image attr (toList ils) (src, "fig:" ++ tit)
               Nothing  -> Image attr alt (src,tit)
        go x = return x

addTikzImageCaption :: PandocMonad m => Blocks -> LP m Blocks
addTikzImageCaption = walkM go
  where go (RawBlock t raw)
            | "\\begin{tikzpicture}" `isPrefixOf` raw = do
          mbcapt <- sCaption <$> getState
          return $ case mbcapt of
               Just ils -> Div ("", ["tikzpicture"], []) [RawBlock t raw, Para (toList ils)]
               Nothing  -> RawBlock t raw
        go x = return x

coloredBlock :: PandocMonad m => String -> LP m Blocks
coloredBlock stylename = try $ do
  skipopts
  color <- braced
  notFollowedBy (grouped inline)
  let constructor = divWith ("",[],[("style",stylename ++ ": " ++ toksToString color)])
  constructor <$> grouped block

graphicsPath :: PandocMonad m => LP m Blocks
graphicsPath = do
  ps <- map toksToString <$> (bgroup *> manyTill braced egroup)
  getResourcePath >>= setResourcePath . (++ ps)
  return mempty

splitBibs :: String -> [Inlines]
splitBibs = map (str . flip replaceExtension "bib" . trim) . splitBy (==',')

alltt :: Blocks -> Blocks
alltt = walk strToCode
  where strToCode (Str s)   = Code nullAttr s
        strToCode Space     = RawInline (Format "latex") "\\ "
        strToCode SoftBreak = LineBreak
        strToCode x         = x

parseListingsOptions :: [(String, String)] -> Attr
parseListingsOptions options =
  let kvs = [ (if k == "firstnumber"
                  then "startFrom"
                  else k, v) | (k,v) <- options ]
      classes = [ "numberLines" |
                  lookup "numbers" options == Just "left" ]
             ++ maybeToList (lookup "language" options
                     >>= fromListingsLanguage)
  in  (fromMaybe "" (lookup "label" options), classes, kvs)

inputListing :: PandocMonad m => LP m Blocks
inputListing = do
  pos <- getPosition
  options <- option [] keyvals
  f <- filter (/='"') . toksToString <$> braced
  dirs <- (splitBy (==':') . fromMaybe ".") <$> lookupEnv "TEXINPUTS"
  mbCode <- readFileFromDirs dirs f
  codeLines <- case mbCode of
                      Just s -> return $ lines s
                      Nothing -> do
                        report $ CouldNotLoadIncludeFile f pos
                        return []
  let (ident,classes,kvs) = parseListingsOptions options
  let language = case lookup "language" options >>= fromListingsLanguage of
                      Just l -> [l]
                      Nothing -> take 1 $ languagesByExtension (takeExtension f)
  let firstline = fromMaybe 1 $ lookup "firstline" options >>= safeRead
  let lastline = fromMaybe (length codeLines) $
                       lookup "lastline" options >>= safeRead
  let codeContents = intercalate "\n" $ take (1 + lastline - firstline) $
                       drop (firstline - 1) codeLines
  return $ codeBlockWith (ident,ordNub (classes ++ language),kvs) codeContents

-- lists

item :: PandocMonad m => LP m Blocks
item = void blocks *> controlSeq "item" *> skipopts *> blocks

descItem :: PandocMonad m => LP m (Inlines, [Blocks])
descItem = do
  blocks -- skip blocks before item
  controlSeq "item"
  optional sp
  ils <- opt
  bs <- blocks
  return (ils, [bs])

listenv :: PandocMonad m => Text -> LP m a -> LP m a
listenv name p = try $ do
  oldInListItem <- sInListItem `fmap` getState
  updateState $ \st -> st{ sInListItem = True }
  res <- env name p
  updateState $ \st -> st{ sInListItem = oldInListItem }
  return res

orderedList' :: PandocMonad m => LP m Blocks
orderedList' = try $ do
  spaces
  let markerSpec = do
        symbol '['
        ts <- toksToString <$> manyTill anyTok (symbol ']')
        case runParser anyOrderedListMarker def "option" ts of
             Right r -> return r
             Left _  -> do
               pos <- getPosition
               report $ SkippedContent ("[" ++ ts ++ "]") pos
               return (1, DefaultStyle, DefaultDelim)
  (_, style, delim) <- option (1, DefaultStyle, DefaultDelim) markerSpec
  spaces
  optional $ try $ controlSeq "setlength"
                   *> grouped (count 1 $ controlSeq "itemindent")
                   *> braced
  spaces
  start <- option 1 $ try $ do pos <- getPosition
                               controlSeq "setcounter"
                               ctr <- toksToString <$> braced
                               guard $ "enum" `isPrefixOf` ctr
                               guard $ all (`elem` ['i','v']) (drop 4 ctr)
                               optional sp
                               num <- toksToString <$> braced
                               case safeRead num of
                                    Just i -> return (i + 1 :: Int)
                                    Nothing -> do
                                      report $ SkippedContent
                                        ("\\setcounter{" ++ ctr ++
                                         "}{" ++ num ++ "}") pos
                                      return 1
  bs <- listenv "enumerate" (many item)
  return $ orderedListWith (start, style, delim) bs

adjustbox :: PandocMonad m => LP m Blocks
adjustbox = do
  bgroup
  kvs <- many1 keyval
  egroup
  case (lookup "tabular" kvs) of
    Just alignStr -> adjustboxTable alignStr
    Nothing -> blocks

adjustboxTable :: PandocMonad m => String -> LP m Blocks
adjustboxTable alignStr = do
  inp <- getInput
  let alignTokens = tokenize $ T.pack $ "{" ++ alignStr ++ "}"
  setInput $ alignTokens ++ inp
  aligns <- parseAligns
  let cols = length aligns
  let widths = replicate cols 0.0
  (header', rows) <- tableContents cols "adjustbox"
  lookAhead $ controlSeq "end" -- make sure we're at end
  return $ table mempty (zip aligns widths) header' rows

-- tables

hline :: PandocMonad m => LP m ()
hline = try $ do
  spaces
  controlSeq "hline" <|>
    -- booktabs rules:
    controlSeq "toprule" <|>
    controlSeq "bottomrule" <|>
    controlSeq "midrule" <|>
    controlSeq "endhead" <|>
    controlSeq "endfirsthead"
  spaces
  optional $ bracketedDumb inline
  return ()

lbreak :: PandocMonad m => LP m Tok
lbreak = (controlSeq "\\" <|> controlSeq "tabularnewline") <* spaces

amp :: PandocMonad m => LP m Tok
amp = symbol '&'

endOrEndOfDocument :: PandocMonad m => Text -> LP m ()
endOrEndOfDocument name = do
  let envEnd = end_ name
  let badDocEnd = unexpectedEndOfDocument name
  if name == "document"
      then envEnd <* many anyTok
      else envEnd <|> badDocEnd <?> "\\end{" ++ (T.unpack name) ++ "}"

unexpectedEndOfDocument :: PandocMonad m => Text -> LP m ()
unexpectedEndOfDocument name =
  lookAhead $ end_ "document" >>
   (report $ UnexpectedEndOfDocument $ T.unpack name)

-- Split a Word into individual Symbols (for parseAligns)
splitWordTok :: PandocMonad m => LP m ()
splitWordTok = do
  inp <- getInput
  case inp of
       (Tok spos Word t : rest) -> do
         setInput $ map (Tok spos Symbol . T.singleton) (T.unpack t) ++ rest
       _ -> return ()

toksToInt :: [Tok] -> Int
toksToInt x = read (toksToString x) :: Int

alignDef :: PandocMonad m => LP m Alignment
alignDef = do
  let cAlign = AlignCenter <$ symbol 'c'
  let lAlign = AlignLeft <$ symbol 'l'
  let rAlign = AlignRight <$ symbol 'r'
  let parAlign = AlignLeft <$ symbol 'p'
  -- aligns from tabularx
  let xAlign = AlignLeft <$ symbol 'X'
  let upperXAlign = AlignLeft <$ symbol 'X'
  let mAlign = AlignLeft <$ symbol 'm'
  let bAlign = AlignLeft <$ symbol 'b'
  -- aligns from tabulary
  let upperLAlign = AlignLeft <$ symbol 'L'
  let upperRAlign = AlignRight <$ symbol 'R'
  let upperCAlign = AlignCenter <$ symbol 'C'
  let upperJAlign = AlignLeft <$ symbol 'J'
  let upperParAlign = AlignLeft <$ symbol 'P'
  let fallbackAlign = AlignLeft <$ anyLetterSymbol
  let questionMarkAlign = AlignLeft <$ symbol '?'

  cAlign <|> lAlign <|> rAlign <|> parAlign
    <|> xAlign <|> upperXAlign <|> mAlign <|> bAlign
    <|> upperLAlign <|> upperRAlign <|> upperCAlign
    <|> upperJAlign <|> upperParAlign
    <|> fallbackAlign <|> questionMarkAlign

singleAlign :: PandocMonad m => LP m Alignment
singleAlign = do
  splitWordTok
  align <- alignDef
  skipopts
  optional braced
  maybeAlignBar
  return align

multipleAlign :: PandocMonad m => LP m [Alignment]
multipleAlign = do
  symbol '*'
  times <- toksToInt <$> braced
  bgroup
  maybeAlignBar
  align <- singleAlign
  spaces
  egroup
  spaces
  maybeAlignBar
  return $ replicate times align

maybeAlignBar :: PandocMonad m => LP m ()
maybeAlignBar = skipMany $
  sp
  <|> () <$ symbol '|'
  <|> () <$ (symbol '@' >> braced)
  <|> () <$ (symbol '>' >> braced)
  <|> () <$ (symbol '<' >> braced)
  <|> () <$ symbol ':'

parseAligns :: PandocMonad m => LP m [Alignment]
parseAligns = try $ do
  bgroup
  spaces
  maybeAlignBar
  let singletonAlign = toList <$> singleton <$> singleAlign
  aligns <- mconcat <$> many (multipleAlign <|> singletonAlign)
  spaces
  egroup
  spaces
  return aligns

tableHeader :: PandocMonad m => Text -> LP m [Blocks]
tableHeader envname = option [] $ try (tableRowCells envname <*
                                   lbreak <* many1 hline)

tableRows :: PandocMonad m => Text -> LP m [[Blocks]]
tableRows envname = sepEndBy (tableRowCells envname) (lbreak <* optional (skipMany hline))

tableRowCells :: PandocMonad m => Text -> LP m [Blocks]
tableRowCells envname = sepEndBy (tableCellBlock envname) amp

tableCellBlock :: PandocMonad m => Text -> LP m Blocks
tableCellBlock envname = mconcat <$> many cellBlocks
  where cellBlocks = environment
           <|> blockCommand
           <|> tableCellParagraph envname
           <|> grouped (tableCellBlock envname)

tableCellParagraph :: PandocMonad m => Text -> LP m Blocks
tableCellParagraph envname = plain <$> mconcat <$> many1 tableCellInline
  where tableCellInline = notFollowedBy tableCellSeparator >> inlineTok
        tableCellSeparator = () <$ amp <|> () <$ lbreak <|> (end_ envname)
        inlineTok = inline <|> (str "\n" <$ many1 newlineTok) <|> (str " " <$ spaces1)

loudTrace :: Show a => a -> a
loudTrace s = trace ("########### " ++ (show s)) s

loudTraceM :: (PandocMonad m, Show a) => a -> LP m a
loudTraceM s = return $ loudTrace s

simpTable :: PandocMonad m => Text -> Bool -> LP m Blocks
simpTable envname hasWidthParameter = try $ do
  when hasWidthParameter $ () <$ (spaces >> tok)
  skipopts
  aligns <- parseAligns
  let cols = length aligns
  let widths = replicate cols 0.0
  (header', rows) <- tableContents cols envname
  lookAhead $ controlSeq "end" -- make sure we're at end
  return $ table mempty (zip aligns widths) header' rows

tableContents :: PandocMonad m => Int -> Text -> LP m ([Blocks], [[Blocks]])
tableContents cols envname = do
  optional $ controlSeq "caption" *> skipopts *> setCaption
  optional lbreak
  spaces
  skipMany hline
  spaces
  header' <- tableHeader envname
  spaces
  rows <- tableRows envname
  spaces
  optional $ controlSeq "caption" *> skipopts *> setCaption
  optional lbreak
  spaces
  let header'' = if null header'
                    then replicate cols mempty
                    else header'
  return (header'', rows)

easyTable :: PandocMonad m => LP m Blocks
easyTable = try $ do
  wrapped (symbol '(') (symbol ')')
  skipopts
  aligns <- parseAligns
  braced
  let cols = length aligns
  let widths = replicate cols 0.0
  (header', rows) <- tableContents cols "TAB"
  lookAhead $ controlSeq "end"
  return $ table mempty (zip aligns widths) header' rows

addTableCaption :: PandocMonad m => Blocks -> LP m Blocks
addTableCaption = walkM go
  where go (Table c als ws hs rs) = do
          mbcapt <- sCaption <$> getState
          return $ case mbcapt of
               Just ils -> Table (toList ils) als ws hs rs
               Nothing  -> Table c als ws hs rs
        go x = return x

thebibliography :: PandocMonad m => LP m Blocks
thebibliography = do
  braced  -- count
  spaces
  divWith ("", ["bibliography"], []) <$> blocks

bibitem :: PandocMonad m => LP m Blocks
bibitem = do
  spaces
  skipopts
  spaces
  ref <- toksToString <$> braced
  let nextItemOrEnd = lookAhead $ controlSeq "bibitem" <|> controlSeq "end"
  toks <- manyTill anyTok nextItemOrEnd
  pstate <- getState
  let constructor = divWith ("", ["bibitem"], [("label", ref)])
  res <- runParserT blocks pstate "bibitem" toks
  case res of
       Right r -> return $ constructor $ r
       Left e -> fail (show e)

arxivBblBibliography :: PandocMonad m => LP m Blocks
arxivBblBibliography = try $ do
  controlSeq "bibliography"
  spaces
  braced
  sources <- getOption readerInputSources
  let firstSource = head $ sources
  let bblFilename = replaceExtension firstSource "bbl"
  insertIncludedFile blocks (tokenize . T.pack) ["."] bblFilename

figwindow :: PandocMonad m => LP m Blocks
figwindow = try $ do
  let toks = drop 4 <$> bracketed
  fig <- parseToksToBlocks toks
  bs <- blocks
  return $ fig <> bs

block :: PandocMonad m => LP m Blocks
block = (mempty <$ spaces1)
    <|> environment
    <|> include
    <|> arxivBblBibliography
    <|> macroDef
    <|> blockCommand
    <|> paragraph
    <|> grouped block

blocks :: PandocMonad m => LP m Blocks
blocks = mconcat <$> many block
