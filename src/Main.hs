
module Main where 

import PiCalculus
import Trans
import Debug.Trace 
import System.Directory
import System.IO
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

data Command = Load String -- load specification
             | Proc -- display current process
             | Spec -- display current specification
             | Transform -- transform current specification
             | Help  -- view available commands
             | Quit -- quit program
             | Unknown -- erroneous command

command str = let res = words str
              in case res of 
                   [":load",f] -> Load f
                   [":proc"] -> Proc
                   [":spec"] -> Spec
                   [":transform"] -> Transform
                   [":help"] -> Help
                   [":quit"] -> Quit
                   _ -> Unknown

help_message = "\n:load filename\tTo load a file\n"++
               ":proc\t\tTo show the current process\n"++
               ":spec\t\tTo show the current specification\n"++
               ":transform\tTo transform the current process\n"++
               ":help\t\tTo print this message\n"++
               ":quit\t\tTo quit\n"

-- REPL ofr main program

main = toplevel Nothing

toplevel spec = do putStr "Pi> "
                   hFlush stdout
                   x <- getLine
                   case command x of 
                      Load f -> let f' = f++".pi"
                                in  do x <- doesFileExist f'
                                       if   x 
                                       then do
                                            c <- readFile f'
                                            case parseSpec c of 
                                               Left s -> do putStrLn ("Err: Could not parse pi-calculus specification in file "++f'++show s)
                                                            toplevel spec
                                               Right s -> do putStrLn ("Loading file: "++f')
                                                             toplevel (Just s)
                                       else do putStrLn ("No such file: "++f') 
                                               toplevel spec
                      Proc -> case spec of 
                                 Nothing -> do putStrLn "No specification loaded" 
                                               toplevel spec
                                 Just (p,d) -> do putStrLn (show p)
                                                  toplevel spec
                      Spec -> case spec of 
                                 Nothing -> do putStrLn "No specification loaded" 
                                               toplevel spec
                                 Just s -> do putStrLn (showSpec s)
                                              toplevel spec
                      Transform -> case spec of
                                      Nothing -> do putStrLn "No specification loaded"
                                                    toplevel spec
                                      Just (p,d) -> let s = residualise (par p Null [] [] d) []
                                                    in  do putStrLn (showSpec s)
                                                           toplevel (Just s)
                      Help -> do putStrLn help_message 
                                 toplevel spec
                      Quit -> return ()
                      Unknown -> do putStrLn "Err: Could not parse command, type ':help' for a list of commands"
                                    toplevel spec

