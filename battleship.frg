#lang forge/bsl

one sig Game {
  initialState: one State,
  next: pfunc State -> State
}

one sig Yes {}

abstract sig Ship {
   length: one Int,
   isOccupying: pfunc Int -> Int -> Yes   
}

sig Destroyer extends Ship {}
sig Battleship extends Ship {}
sig Submarine extends Ship {}

abstract sig Fleet {
    destroyer: one Destroyer,    
    battleship: one Battleship,    
    submarine: one Submarine
}

--A occupies top half of board, B bottom half
one sig A, B extends Fleet {}

--board is 20x10 map of attacks
sig State {
    board: pfunc Int -> Int -> Fleet
}

pred wellformed {    
    --ships are within the bounds of the respective board
    all row, col: Int | {
        (some A.destroyer.isOccupying[row][col] or        
        some A.battleship.isOccupying[row][col] or        
        some A.submarine.isOccupying[row][col]) => {
            row >= 0 and row < 5
            col >= 0 and col < 5
        }

        (some B.destroyer.isOccupying[row][col] or        
        some B.battleship.isOccupying[row][col] or     
        some B.submarine.isOccupying[row][col]) => {
            row >= 0 and row < 5
            col >= 5 and col < 10
        }
    }
    --ships are of proper length and composed of adjacent coords
    all s: Ship | {
        #{row, col: Int | some s.isOccupying[row][col]} = s.length        
        all r1, r2, c1, c2: Int | {            
            (some s.isOccupying[r1][c1] and some s.isOccupying[r2][c2]) => {
                (abs[r1 - r2] < s.length and c1 = c2) or
                (abs[c1 - c2] < s.length and r1 = r2)
            }
        } 
    }
    --ships are not overlapping
    all disj s1, s2: Ship | {
        all row, col: Int | {
            some s1.isOccupying[row][col] =>
            no s2.isOccupying[row][col]
        }
    }
}

pred lengths {
    all f: Fleet | {
        f.destroyer.length = 2
        f.submarine.length = 3
        f.battleship.length = 4        
    }
}

pred init[s: State] {
    -- all board outputs are none    
    all row, col: Int | {
        no s.board[row][col]
    }
}

pred ATurn[s: State] {
  #{row, col: Int | s.board[row][col] = A} =
  #{row, col: Int | s.board[row][col] = B}
}

pred BTurn[s: State] {
  #{row, col: Int | s.board[row][col] = A} =
  add[#{row, col: Int | s.board[row][col] = B}, 1]
}

pred validTransition[pre: State, post: State] {    
    --all attacks from pre state are present in post
    all row, col: Int | {
        some pre.board[row][col] => some post.board[row][col]
    }
    #{row, col: Int | some post.board[row][col]} = add[1, #{row, col: Int | some pre.board[row][col]}]
    --there's one new attack and it's valid
    one row, col: Int | {
        some post.board[row][col]
        no pre.board[row][col]
        post.board[row][col] = A => {
            ATurn[pre]
            row >= 0 and row < 5
            col >= 5 and col < 10
        }
        else {
            BTurn[pre]
            row >= 0 and row < 5
            col >= 0 and col < 5
        }
    }
}

pred gameOver[s : State] {
    some disj w, l: Fleet | {
        all row, col: Int | {
            (some l.destroyer.isOccupying[row][col] or            
            some l.battleship.isOccupying[row][col] or            
            some l.submarine.isOccupying[row][col]) =>
            s.board[row][col] = w
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

// example validStart is init for {
   
// }

-- traces of State
run {
  wellformed
  traces
  lengths
} for exactly 2 Destroyer, exactly 2 Battleship, exactly 2 Submarine, 
    5 Int, 3 State for {next is linear}