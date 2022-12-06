{-# LANGUAGE OverloadedStrings #-}
import qualified Data.Text as T
import System.IO


wall = 'W'
ground = ' '
storage = 'X'
box = '#'
blank = ' '
playerU = '^'
playerD = 'v'
playerR = '>'
playerL = '<'

startScreen = "Sokoban!"
endScreen = "That's all!!!"
betweenScreen i = (mappend "Level finished, number of moves: " (show i))

drawTile Wall    = wall
drawTile Ground  = ground
drawTile Storage = storage
drawTile Box     = box
drawTile Blank   = blank

data Tile = Wall | Ground | Storage | Box | Blank
  deriving (Eq, Show)
data Coord = Co {pointx, pointy :: Double}
  deriving (Eq, Show)
data Direction = R | U | L | D
  deriving (Eq, Show)

data Maze = Maze  {
  pos :: Coord,
  mzMap :: (Coord -> Tile)
}
data State = S {
  stDir    :: Direction,
  stBoxes  :: [Coord],
  stMap    :: Maze,
  stXMin   :: Integer,
  stXMax   :: Integer,
  stYMin   :: Integer,
  stYMax   :: Integer
}

instance Eq State where
  S dir boxes (Maze start fun) xmin xmax ymin ymax ==  S dir' boxes' (Maze start' fun') xmin' xmax' ymin' ymax' =
     dir == dir' && boxes == boxes' && xmin == xmin' && xmax == xmax' && ymin == ymin' && ymax == ymax' && start == start'
     && andList [(fun (Co (fromInteger x) (fromInteger y)) == fun' (Co (fromInteger x) (fromInteger y)))| x <- [xmin..xmax], y <- [ymin..ymax] ]


data SSState world = StartScreen | Running world
  deriving (Eq)

data Activity world = Activity {
    actState  :: world,
    actHandle :: (Event -> world -> world),
    actDraw   ::(world -> Screen)
}

data Event = KeyPress String
type Screen = String

data GameState = Levels | Playing {level :: State} | ScreenBetween { i :: Integer}| EndScreen
  deriving (Eq)

data Game = Game {
    currentAct :: GameState,
    maps :: [Maze],
    count :: Integer
}

{- Since there only ever will be one maps list, we can ignore it-}
instance Eq Game where
  Game currentAct maps count ==   Game currentAct' maps' count' = currentAct == currentAct'

drawingOfLevels = pictureOfBools (mapList (\x -> isClosed x && isSane x) (mazes))

drawGame game = drawGameState (currentAct game)

drawGameState Levels = appendList "Lista poziomów\n" drawingOfLevels

drawGameState EndScreen = endScreen

drawGameState (ScreenBetween i) = betweenScreen i

drawGameState (Playing world) = draw world


drawingOf drawing minx miny maxx maxy = drawingOfHelp drawing minx maxy maxx maxx miny []

drawingOfHelp drawing minx maxy maxx x y acc =
  if (x == minx && y == maxy) then ((drawing x y):acc)
  else if x == minx - 1 then drawingOfHelp drawing minx maxy maxx maxx (y + 1) (('\n'):acc)
  else drawingOfHelp drawing minx maxy maxx (x - 1) y ((drawing x y):acc)


draw world = drawingOf maze (fromInteger (stXMin world))  (fromInteger (stYMin world))  (fromInteger (stXMax world))  (fromInteger (stYMax world)) where
  maze = (getPlayer (pos (stMap world)) (stDir world) & getBoxes (stBoxes world) & pictureOfMaze (mzMap (stMap world)) [(Co (fromInteger x) (fromInteger y))| x <- [(stXMin world)..(stXMax world)], y <- [(stYMin world)..(stYMax world)]] )  none

(&) = (.)

none x y = blank

worldFromMaze maze = S U (boxesLoc maze (-10) 10 (-10) 10) maze{ mzMap = removeBoxes (mzMap maze)} (-10) 10 (-10) 10

baseGame = Game Levels (appendList goodMazes badMazes) 0

handleGame (KeyPress key) (Game currentAct maps count)
    | key == "n" = skipLevel (Game currentAct maps count)
    | key == " " = nextStage (Game currentAct maps count)
    | otherwise = passToWorld (KeyPress key) (Game currentAct maps count)
handleGame _ c      = c

nextStage (Game (ScreenBetween i) (next:rest) count) = (Game (Playing (worldFromMaze next)) rest count)
nextStage (Game (ScreenBetween i) [] count) = (Game EndScreen [] count)
nextStage (Game (Levels) (next:rest) count) = (Game (Playing (worldFromMaze next)) rest count)
nextStage c = c

skipLevel (Game (Playing world) (next:rest) count) = (Game (Playing (worldFromMaze next)) rest 0)
skipLevel (Game (Playing world) [] count) = (Game EndScreen [] count)
skipLevel c = c

passToWorld event (Game (Playing world) rest count) = nextStage
    where
    world' = handleEventWalk event world
    nextStage = if isWinning world' then (Game (ScreenBetween (count + 1)) rest 0)
      else if world' /= world then (Game (Playing world') rest (count + 1))
      else (Game (Playing world') rest count)

passToWorld e c = c


elemList el list = foldList (\x y -> x == el || y) False list

appendList a b = foldList (\x y -> x:y) b (reverse a)

listLength list = foldList (\x y -> y + 1) 0 list

filterList crit list = reverse (foldList (\x y -> if (crit x) then x:y else y) [] list)

nth (el:rest) n = snd (foldList (\x (a,b) -> if a == -1 then (a,b) else ( a - 1,x)) (n - 1, el) rest)


mapList fun list = reverse (foldList (\x y -> (fun x):y) [] list)

andList list = foldList (\x y -> x && y) True list

orList list = foldList (\x y -> x || y) True list

allList eval list = foldList (\x y -> eval x && y) True list

sumList list = foldList (\x y -> x + y) 0 list

foldList fun acc [] = acc
foldList fun acc (el:rest) = foldList fun (fun el acc) rest

isGraphClosedHelp (start:rest) next crit visited =
   if elemList start visited then isGraphClosedHelp rest next crit visited
   else if not (crit start) then False
   else isGraphClosedHelp (appendList rest (next start)) next crit (start:visited)

isGraphClosedHelp [] next crit visited = True

isGraphClosed initial neighbours isOk = isGraphClosedHelp [initial] neighbours isOk []

reachable v initial neighbours = not (isGraphClosed initial neighbours (\x -> x /= v))

reachableCountHelp crit (start:rest) next visited =
   if elemList start visited then reachableCountHelp crit rest next visited
   else if crit start then 1 + neighSum
   else neighSum
   where
   neighSum = reachableCountHelp crit (appendList rest (next start)) next (start:visited)
   
reachableCountHelp crit  [] next visited = 0

reachableCount crit initial neighbours = reachableCountHelp crit [initial] neighbours []

{-Dopuszczamy skanowanie przez pudła, ponieważ przesunięcie ich może doprowadzić nas do blanka-}
isClosed (Maze pos maze) = (maze pos == Storage || maze pos == Ground) && isGraphClosed pos (\x -> if (maze x == Wall) then [] else (getAllAdjecentCoord x)) (\x -> maze x /= Blank)
isSane (Maze pos maze) = countTile Box == countTile Storage
  where
  countTile tile = reachableCount (\x -> (maze x == tile)) pos (\x -> if (maze x == Wall) then [] else (getAllAdjecentCoord x))


allReachable vs initial neighbours = andList (mapList (\x -> reachable x initial neighbours) vs)
   
goodMaze1map coord
  | abs (pointx coord) > 4  || abs (pointy coord) > 4  = Blank
  | abs (pointx coord) == 4 || abs (pointy coord) == 4 = Wall
  | (pointx coord) ==  2 && (pointy coord) <= 0        = Wall
  | (pointx coord) ==  3 && (pointy coord) <= 0        = Storage
  | (pointx coord) >= -2 && (pointy coord) == 0        = Box
  | otherwise                = Ground
goodMaze1 = Maze (Co 0 1) goodMaze1map

goodMaze2map coord
  | pointx coord > 3 || pointx coord < -4 || abs (pointy coord) > 3  = Blank
  | pointx coord == 3 || pointx coord == -4 || abs (pointy coord) == 3 = Wall
  | (pointx coord) ==  -1 && abs(pointy coord) == 2 = Wall
  | (pointx coord) ==  2 && abs(pointy coord) == 0 = Wall
  | (pointx coord == -1 || pointx coord == 0) && abs (pointy coord) <= 1   = Storage
  | (pointx coord == -2 || pointx coord == 1) && abs (pointy coord) <= 1     = Box
  | otherwise                = Ground

goodMaze2 = Maze (Co (-3) 1) goodMaze2map

goodMaze3map coord
  | pointx coord > 3 || pointx coord < -4 || abs (pointy coord) > 3  = Blank
  | pointx coord == 3 || pointx coord == -4 || abs (pointy coord) == 3 = Wall
  | (pointx coord) ==  2 && ((pointy coord) >= 1 || (pointy coord) <= -2) = Wall
  | (pointx coord) <= -2 && ((pointy coord) >= 2 || (pointy coord) <= -1) = Wall
  | abs (pointx coord) + abs (pointy coord) ==  1      = Storage
  | (pointx coord) + (pointy coord) == 0 || coord == Co (-2) (1)     = Box
  | otherwise                = Ground

goodMaze3 = Maze (Co 0 1) goodMaze3map

goodMaze4map coord
  | pointy coord < -3 || pointy coord > 4 || abs (pointx coord) > 3  = Blank
  | pointy coord == -3 || pointy coord == 4 || abs (pointx coord) == 3 = Wall
  | coord == Co (0) (2) || coord == Co (0) (-2) = Wall
  | pointy coord >=  2 && pointx  coord /= 0   = Storage
  | pointx coord == 0 || (abs (pointy coord) == 1 && abs (pointx coord) == 1) = Box
  | otherwise                = Ground

goodMaze4 = Maze (Co (-2) 0) goodMaze4map


goodMaze5map coord
  | abs (pointx coord) > 4  || abs (pointy coord) > 4  = Blank
  | abs (pointx coord) == 4 || abs (pointy coord) == 4 = Wall
  | (pointx coord) + (pointy coord) ==  0          = Wall
  | (pointx coord) ==  -2 && (pointy coord) == -2     = Storage
  | (pointx coord) ==  2 && (pointy coord) == 2         = Box
  | (pointx coord) ==  -1 && (pointy coord) == -1         = Box
  | otherwise                = Ground
 
goodMaze5 = Maze (Co (-2) (-2)) goodMaze5map


badMaze1map coord
  | abs (pointx coord) > 4  || abs (pointy coord) > 4  = Blank
  | abs (pointx coord) == 4 || abs (pointy coord) == 4 = Wall
  | (pointx coord) ==  2 && (pointy coord) <= 0        = Wall
  | (pointx coord) ==  3 && (pointy coord) <= 0        = Storage
  | (pointx coord) >= -1 && (pointy coord) == 0        = Box
  | otherwise                = Ground
 
badMaze1 = Maze (Co 0 1) badMaze1map

badMaze2map coord
  | abs (pointx coord) > 4  || abs (pointy coord) > 4  = Blank
  | abs (pointx coord) == 4 || abs (pointy coord) == 4 = Wall
  | (pointx coord) ==  2       = Wall
  | (pointx coord) ==  3 && (pointy coord) <= 0        = Storage
  | (pointx coord) >= -2 && (pointy coord) == 0        = Box
  | otherwise                = Ground

badMaze2 = Maze (Co 0 1) badMaze2map
 
badMaze3map coord
  | abs (pointx coord) > 4  || abs (pointy coord) > 1  = Blank
  | (pointx coord) ==  2       = Blank
  | abs (pointx coord) == 4 || abs (pointy coord) == 1 = Wall
  | (pointx coord) ==  3        = Storage
  | (pointx coord) == -1        = Box
  | otherwise                = Ground
 
badMaze3 = Maze (Co (-2) 0) badMaze3map

goodMazes = [goodMaze1, goodMaze2, goodMaze3, goodMaze4, goodMaze5]
badMazes = [badMaze1, badMaze2, badMaze3]

mazes = goodMazes ++ badMazes

pictureOfBools xs = mapList (\x -> if x then 'O' else 'X') xs

boxesLoc (Maze pos mazeMap) xMin xMax yMin yMax = [(Co x y)| x <- [xMin..xMax], y <- [yMin..yMax], mazeMap (Co x y) == Box && reachable pos (Co x y) (\x -> getNonWalls mazeMap x)]
 
moveBox toMove dir world = world{stBoxes = (adjacentCoord dir toMove):(filterList (\box -> box /= toMove) (stBoxes world))}

checkForCollision world dir =
  if mazeMap next == Wall || ((mazeMap next == Box) && ((mazeMap nextNext == Wall) || (mazeMap nextNext == Box))) then world{stDir = dir}
  else if (mazeMap next == Box) then moveBox next dir world{stDir = dir, stMap = (stMap world){pos = next}}
  else world {stDir = dir, stMap = (stMap world){pos = next}}
  where
  mazeMap = addBoxes (stBoxes world) (mzMap (stMap world))
  next = adjacentCoord dir (pos (stMap world))
  nextNext = adjacentCoord dir next
 
adjacentCoord dir coord = case dir of
    R -> coord {pointx = pointx coord + 1}
    U -> coord {pointy = pointy coord + 1}
    L -> coord {pointx = pointx coord - 1}
    D -> coord {pointy = pointy coord - 1}

getAllAdjecentCoord coord = [(adjacentCoord x coord)| x<- [R,U,L,D] ]

getNonWalls maze coord = [(adjacentCoord x coord)| x<- [R,U,L,D], maze (adjacentCoord x coord) /= Wall && maze (adjacentCoord x coord) /= Blank]

 
pictureOfMaze maze ((Co x y):restPoints) picture picx picy
  | restPoints == [] = picture picx picy
  | otherwise = if x == picx && y == picy then drawTile (maze (Co x y)) else pictureOfMaze maze restPoints picture picx picy
 
 
getBoxes ((Co x y):rest) picture picx picy = if x == picx && y == picy then drawTile (Box) else getBoxes rest picture picx picy

getBoxes [] picture picx picy = picture picx picy
 
getDirSprite dir = case dir of
    R -> playerR
    U -> playerU
    L -> playerL
    D -> playerD

getPlayer (Co x y) dir picture picx picy = if x == picx && y == picy then getDirSprite dir else picture picx picy

removeBoxes mazeMap coord =
  if field == Box then Ground else field
  where field = mazeMap coord
 
addBoxes (box:rest) mazeMap coord
  | box == coord = Box
  | otherwise = addBoxes rest mazeMap coord

addBoxes [] mazeMap coord = mazeMap coord

checkBoxes mazeMap (box:rest) =
  if not (mazeMap box == Storage) then False
  else checkBoxes mazeMap rest
 
checkBoxes mazeMap [] = True

isWinning world = if (stBoxes world) == [] then False else checkBoxes (mzMap (stMap (world))) (stBoxes world)


handleEventWalk (KeyPress key) world
    | isWinning world = world
    | key == "d" = go R
    | key == "w"    = go U
    | key == "a"  = go L
    | key == "s"  = go D
    where
      go d = checkForCollision world d
handleEventWalk _ c      = c

resettable (Activity state0 handle draw)
  = Activity state0 handle' draw
  where handle' (KeyPress key) _ | key == "r" = state0
        handle' e s = handle e s

data WithUndo a = WithUndo a [a]

withUndo :: Eq a => Activity a -> Activity (WithUndo a)
withUndo (Activity state0 handle draw) = Activity state0' handle' draw' where
    state0' = WithUndo state0 []
    handle' (KeyPress key) (WithUndo s stack) | key == "u"
      = case stack of s':stack' -> WithUndo s' stack'
                      []        -> WithUndo s []
    handle' e              (WithUndo s stack)
       | s' == s = WithUndo s stack
       | otherwise = WithUndo (handle e s) (s:stack)
      where s' = handle e s
    draw' (WithUndo s _) = draw s

withStartScreen (Activity state0 handle draw)
  = Activity state0' handle' draw'
  where
    state0' = StartScreen

    handle' (KeyPress key) StartScreen
         | key == " "                  = Running state0
    handle' _              StartScreen = StartScreen
    handle' e              (Running s) = Running (handle e s)

    draw' StartScreen = startScreen
    draw' (Running s) = draw s

{-We treat press of r as reset, so we don't care about it releasing -}
handlerResetWrapper handler baseWorld (KeyPress key) world
    | key == "r" = baseWorld
    | otherwise = (handler (KeyPress key) world)
handlerResetWrapper h bw _ w  = w


gameActivity = Activity baseGame handleGame drawGame
etap5 = runActivity (withUndo (resettable (withStartScreen gameActivity)))

{- we reset to start screen-}
runActivity (Activity state0 handle draw) = activityOf state0 handle draw


{- this allows to play with arrows and WASD both -}
changeToWASD char 
  | char == 'A' = "w"
  | char == 'B' = "s"
  | char == 'C' = "d"
  | char == 'D' = "a"
  | otherwise = "None"

getKey = do
  char <- getChar
  if char == '\ESC' then do
    char2 <- getChar
    if char2 == '[' then do
      char3 <- getChar
      return (KeyPress (changeToWASD char3))
    else
      return (KeyPress "None")
  else
    return (KeyPress [char])

activityOf state0 handle draw = do 
	putStr "\ESCc"
  	hSetBuffering stdout NoBuffering
	putStrLn (draw state0)
  	hSetBuffering stdin NoBuffering
	key <- getKey
	
	activityOf (handle key state0) handle draw

main :: IO ()
main = etap5
