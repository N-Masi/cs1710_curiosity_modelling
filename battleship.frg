one sig Yes {}

sig Coordinate {
    x: one Int
    y: one Int
}

sig Ship {
   length: one Int
   isOccupying: pfunc Coordinate -> Yes   
}

abstract sig Fleet {
    destroyer: one Ship
    carrier: one Ship
    battleship: one Ship
    cruiser: one Ship
    submarine: one Ship
}

--A occupies top half of board, B bottom half
one sig A, B extends Fleet {}

--board is 20x10 map of attacks
sig State {
    board: pfunc Int -> Int -> Yes
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
        no c: Coordinate | {
            s1.isOccupying[c] = Yes
            s2.isOccupying[c] = Yes
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
    -- one of each ship type per board
}

pred validTransition[pre: State, post: State] {
    -- for all ships, partOfShip is exactly the same
    -- only one Outcome changes on one board func
    -- the board which changes alternates between turns
    -- attack that was taken was on input ints 0<=10
}

pred gameOver[s : State] {
    
}

pred noMove[pre: State, post: State] {

}

-- traces of State
run {
    -- enforce init on some start state
    -- enforce wellformed on all states
    -- enforce validTransition between states
    -- enfore gameOver on some state
    -- enfore noMove on all states after gameOver
} for 5 Int