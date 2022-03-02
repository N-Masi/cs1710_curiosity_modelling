#lang forge/bsl

one sig Game {
  initialState: one State,
  next: pfunc State -> State
}

// doing this rather than a pfunc that takes two Int
// as input allows us to count the number of Coordinates
// that have a certain property (e.g., such as being 
// part of a ship)
sig Coordinate {
    x: one Int,
    y: one Int
}

// this lets us make psuedo-sets
one sig Yes {}

sig Ship {
   // this is a set of the coordinates part of the ship
   isOccupying: pfunc Coordinate -> Yes,
   // this is how many coordinates the ship takes up
   length: one Int
}

// each player has a fleet, they're one in the same in our
// model and each fleet has one destroyer
abstract sig Fleet {
    destroyer: one Ship
}

-- A occupies left half of board, B right half
one sig A, B extends Fleet {}

-- board is 6x3 map of attacks
sig State {
    board: pfunc Coordinate -> Fleet
}

// all coordinates are in the board from 0-2 in the y
// and 0-5 in the x
pred inBoundsCoordinates {
    no c: Coordinate | {
        -- board is 3 high by 6 wide (two 3x3 boards lined up
        -- horizontally to represent the two players)
        c.y < 0 or c.y > 2 or c.x < 0 or c.x > 5
    }
}

// each coordinate is unique
pred noDuplicateCoordinates {
    no disj c1, c2 : Coordinate |
            c1.x = c2.x and c1.y = c2.y  
}

// fleets don't use the same ship
pred differentShipsInEachFleet {
    no s: Ship | {
        A.destroyer = s and B.destroyer = s
    }
}

pred wellformed {
    -- ships are within the bounds of the respective board
    all c: Coordinate | {
        -- A's ships have to be on left half
        (A.destroyer.isOccupying[c] = Yes) => {
            c.x >= 0 and c.x <3
            c.y >= 0 and c.y <3
        }
        -- B's ships have to be on the right half
        (B.destroyer.isOccupying[c] = Yes) => {
            c.x >= 3 and c.x <6
            c.y >= 0 and c.y <3
        }
    }
    -- ships are of proper length and composed of adjacent coords
    all s: Ship | {
        #{c: Coordinate | s.isOccupying[c] = Yes} = s.length -- this is causing unsat     
        all disj c1, c2: Coordinate | {
            (s.isOccupying[c1] = Yes and s.isOccupying[c2] = Yes) => {
                (abs[c1.x - c2.x] < s.length and c1.y = c2.y) or
                (abs[c1.y - c2.y] < s.length and c1.x = c2.x)
            }
        }        
    }
    -- A and B attacks confined to their sides
    all c: Coordinate | {
        all s: State | {
            s.board[c] = A
                => c.x < 3
            s.board[c] = B
                => c.x >= 3
        }
    }
    -- make sure we have exactly the 18 coordinates
    -- we want for our 3x6 board
    inBoundsCoordinates
    noDuplicateCoordinates
    -- make sure fleets have different instances of ships
    differentShipsInEachFleet
}

// make the length of ships what they actually are
// in the boardgame Battleship
pred lengths {
    all f: Fleet | {
        f.destroyer.length = 2
    }
}

pred init[s: State] {
    -- all board outputs are none    
    all c: Coordinate | {
        s.board[c] = none
    }
}

pred ATurn[s: State] {
  #{c: Coordinate | s.board[c] = A} =
  #{c: Coordinate | s.board[c] = B}
}

pred BTurn[s: State] {
  #{c: Coordinate | s.board[c] = A} =
  add[#{c: Coordinate | s.board[c] = B}, 1]
}

pred validTransition[pre: State, post: State] {    
    -- all attacks from pre state are present in post
    all c: Coordinate | {
        pre.board[c] != none
            => pre.board[c] = post.board[c]
    }
    -- there's one new attack and it's valid
        -- check attacks by A
    ATurn[pre] => {
        #{c: Coordinate | {
            pre.board[c] = none and
            post.board[c] = A
        }} = 1 and
        #{c: Coordinate | {
            pre.board[c] = none and
            post.board[c] = B 
        }} = 0
    }
        -- check attacks by B
    BTurn[pre] => {
        #{c: Coordinate | {
            pre.board[c] = none and
            post.board[c] = A
        }} = 0 and
        #{c: Coordinate | {
            pre.board[c] = none and
            post.board[c] = B 
        }} = 1
    }
}

// true if a player/fleet's ships are all sunk
pred gameOver[s : State] {
    some f: Fleet | {
        all c: Coordinate | {
            (f.destroyer.isOccupying[c] = Yes) =>
                s.board[c] = f
        }
    }
}

// replacement for validTransistion (between states)
// if the game is over
pred doNothing[pre: State, post: State] {
    gameOver[pre] -- guard of the transition
    -- pre.board = post.board -- effect of the transition
    all c : Coordinate |
        pre.board[c] = post.board[c]
}

pred traces {
    -- The trace starts with an initial state
    init[Game.initialState]
    no sprev: State | Game.next[sprev] = Game.initialState
    -- Every transition is a valid move
    all s: State | some Game.next[s] implies {
        gameOver[s] 
            => doNothing[s, Game.next[s]]
            else validTransition[s, Game.next[s]]
    } 
}

test expect {
    gameOverAchievable: {
        lengths
        wellformed
        traces
        some s: State | {
            gameOver[s]
        }
    } for exactly 18 Coordinate, exactly 2 Ship, 4 Int for {next is linear} is sat
}

-- traces of State
run {
  lengths
  wellformed
  traces
} for exactly 18 State, exactly 18 Coordinate, exactly 2 Ship, 4 Int for {next is linear}