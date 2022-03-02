#lang forge/bsl

one sig Game {
  initialState: one State,
  next: pfunc State -> State
}

sig Coordinate {
    x: one Int,
    y: one Int
}

one sig Yes {}

sig Ship {
   length: one Int,
   isOccupying: pfunc Coordinate -> Yes   
}

abstract sig Fleet {
    destroyer: one Ship
}

--A occupies left half of board, B right half
one sig A, B extends Fleet {}

pred differentShipsInEachFleet {
    no s: Ship | {
        A.destroyer = s and B.destroyer = s
    }
}

--board is 6x3 map of attacks
sig State {
    board: pfunc Coordinate -> Fleet
}

pred wellformed {
    --ships are within the bounds of the respective board
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
    --ships are of proper length and composed of adjacent coords
    all s: Ship | {
        #{c: Coordinate | s.isOccupying[c] = Yes} = s.length -- this is causing unsat     
        all disj c1, c2: Coordinate | {
            (s.isOccupying[c1] = Yes and s.isOccupying[c2] = Yes) => {
                (abs[c1.x - c2.x] < s.length and c1.y = c2.y) or
                (abs[c1.y - c2.y] < s.length and c1.x = c2.x)
            }
        }        
    }
    // --ships are not overlapping
    // all disj s1, s2: Ship | {
    //     all c: Coordinate | {
    //         (s1.isOccupying[c] = Yes) =>
    //         no s2.isOccupying[c]
    //     }
    // }
}

pred Lengths {
    all f: Fleet | {
        f.destroyer.length = 2
    }
}

pred inBoundsCoordinates {
    no c: Coordinate | {
        -- board is 3 high by 6 wide (two 3x3 boards lined up
        -- horizontally to represent the two players)
        c.y < 0 or c.y > 2 or c.x < 0 or c.x > 5
    }
}

pred noDuplicateCoordinates {
    no disj c1, c2 : Coordinate |
            c1.x = c2.x and c1.y = c2.y  
}

pred init[s: State] {
    -- all board outputs are none    
    all c: Coordinate | {
        no s.board[c]
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
    --all attacks from pre state are present in post
    all c: Coordinate | {
        pre.board[c] != none
            => pre.board[c] = post.board[c]
    }
    --there's one new attack and it's valid
    add[#{c: Coordinate | {
        post.board[c] != none
        pre.board[c] = none
        post.board[c] = A => {
            ATurn[pre]
            c.x >= 0 and c.x < 3
            c.y >= 0 and c.y < 3
        }
    }},
    #{c: Coordinate | {
        post.board[c] != none
        pre.board[c] = none
        post.board[c] = B => {
            BTurn[pre]
            c.x >= 3 and c.x < 6
            c.y >= 0 and c.y < 3
        }
    }}] = 1
}

pred gameOver[s : State] {
    some disj w, l: Fleet | {
        all c: Coordinate | {
            (l.destroyer.isOccupying[c] = Yes) =>
            s.board[c] = w
        }
    }
}

pred doNothing[pre: State, post: State] {
    gameOver[pre] -- guard of the transition
    --pre.board = post.board -- effect of the transition
    all c : Coordinate |
        pre.board[c] = post.board[c]
}

pred traces {
    -- The trace starts with an initial state
    init[Game.initialState]
    no sprev: State | Game.next[sprev] = Game.initialState
    -- Every transition is a valid move
    all s: State | some Game.next[s] implies {
        validTransition[s, Game.next[s]]
        //or (gameOver[s] and doNothing[s, Game.next[s]]) 
    } 
}

-- traces of State
run {
  Lengths
  inBoundsCoordinates
  noDuplicateCoordinates
  differentShipsInEachFleet
  wellformed
  traces
} for 10 State, exactly 18 Coordinate, exactly 2 Ship, 4 Int for {next is linear}