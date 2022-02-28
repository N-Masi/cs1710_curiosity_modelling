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
    destroyer: one Ship,
    carrier: one Ship,
    battleship: one Ship,
    cruiser: one Ship,
    submarine: one Ship
}

--A occupies top half of board, B bottom half
one sig A, B extends Fleet {}

--board is 20x10 map of attacks
sig State {
    board: pfunc Coordinate -> Fleet
}

pred wellformed {
    --ships are within the bounds of the respective board
    all c: Coordinate | {
        (A.destroyer.isOccupying[c] = Yes or
        A.carrier.isOccupying[c] = Yes or
        A.battleship.isOccupying[c] = Yes or
        A.cruiser.isOccupying[c] = Yes or
        A.submarine.isOccupying[c] = Yes) => {
            c.x >= 0 and c.x <10
            c.y >= 0 and c.y <10
        }

        (B.destroyer.isOccupying[c] = Yes or
        B.carrier.isOccupying[c] = Yes or
        B.battleship.isOccupying[c] = Yes or
        B.cruiser.isOccupying[c] = Yes or
        B.submarine.isOccupying[c] = Yes) => {
            c.x >= 0 and c.x <10
            c.y >= 10 and c.y <20
        }
    }
    --ships are of proper length and composed of adjacent coords
    all s: Ship | {
        #{c: Coordinate | s.isOccupying[c] = Yes} = s.length        
        all disj c1, c2: Coordinate | {
            (s.isOccupying[c1] = Yes and s.isOccupying[c2] = Yes) => {
                (abs[c1.x - c2.x] < s.length and c1.y = c2.y) or
                (abs[c1.y - c2.y] < s.length and c1.x = c2.x)
            }
        }        
    }
    --ships are not overlapping
    all disj s1, s2: Ship | {
        all c: Coordinate | {
            (s1.isOccupying[c] = Yes) =>
            no s2.isOccupying[c]
        }
    }
}

pred Lengths {
    all f: Fleet | {
        f.destroyer.length = 2
        f.carrier.length = 5
        f.battleship.length = 4
        f.cruiser.length = 3
        f.submarine.length = 3
    }
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
        pre.board[c] = post.board[c]
    }
    --there's one new attack and it's valid
    one c: Coordinate | {
        some post.board[c]
        no pre.board[c]
        post.board[c] = A => {
            ATurn[pre]
            c.x >= 0 and c.x < 10
            c.y >= 10 and c.y < 20
        }
        else {
            BTurn[pre]
            c.x >= 0 and c.x < 10
            c.y >= 0 and c.y < 10
        }
    }
}

pred gameOver[s : State] {
    some disj w, l: Fleet | {
        all c: Coordinate | {
            (l.destroyer.isOccupying[c] = Yes or
            l.carrier.isOccupying[c] = Yes or
            l.battleship.isOccupying[c] = Yes or
            l.cruiser.isOccupying[c] = Yes or
            l.submarine.isOccupying[c] = Yes) =>
            s.board[c] = w
        }
    }
}

pred doNothing[pre: State, post: State] {
    gameOver[pre] -- guard of the transition
    pre.board = post.board -- effect of the transition
}

pred traces {
    -- The trace starts with an initial state
    init[Game.initialState]
    no sprev: State | Game.next[sprev] = Game.initialState
    -- Every transition is a valid move
    all s: State | some Game.next[s] implies {
        validTransition[s, Game.next[s]] or
        doNothing[s, Game.next[s]]      
    } 
}

-- traces of State
run {
  wellformed
  traces
  Lengths
} for 20 State for {next is linear}