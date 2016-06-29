module Main where

import qualified Data.Text
import           PrettyPrint              (pprint)
import           Source.Parser            (parseExpr)
import           System.Console.Haskeline
import           Target.TypeCheck
import           Translation              (translate)


main :: IO ()
main = runInputT defaultSettings loop
  where loop :: InputT IO ()
        loop =
          do minput <- getInputLine "> "
             case minput of
               Nothing -> return ()
               Just "" -> loop
               Just ":q" -> return ()
               Just cmds -> dispatch cmds
        dispatch :: String -> InputT IO ()
        dispatch cmds =
          let e@(cmd:progm) = words cmds
          in case cmd of
               _ ->
                 processCMD e $
                 \xs ->
                   do emptyLine
                      outputStrLn "Abstract syntax"
                      outputStrLn $ show xs
                      emptyLine
                      outputStrLn "Pretty printing"
                      outputStrLn $ pprint xs
                      emptyLine
                      outputStrLn "Source typing result"
                      case translate xs of
                        Left err -> printText err
                        Right (typ, targetExpr) -> do
                          outputStrLn $ pprint typ
                          emptyLine
                          outputStrLn "Target expression after translation"
                          outputStrLn $ pprint targetExpr
                          emptyLine
                          outputStrLn "Target typing result"
                          case typecheck targetExpr of
                            Left err -> printText err
                            Right t -> outputStrLn $ pprint t
                          emptyLine
                          outputStrLn "Target evaluation result"
                          outputStrLn $ pprint $ eval targetExpr
          where processCMD expr func =
                  do case parseExpr . unwords $ expr of
                       Left err -> outputStrLn . show $ err
                       Right xs -> func xs
                     emptyLine
                     loop
                emptyLine = outputStrLn ""
                printText = outputStrLn . Data.Text.unpack
