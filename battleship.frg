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
        (A.destroyer.isOccupying[c] or
        A.carrier.isOccupying[c] or
        A.battleship.isOccupying[c] or
        A.cruiser.isOccupying[c] or
        A.submarine.isOccupying[c]) => {
            c.x >= 0 and c.x <10
            c.y >= 0 and c.y <10
        }

        (B.destroyer.isOccupying[c] or
        B.carrier.isOccupying[c] or
        B.battleship.isOccupying[c] or
        B.cruiser.isOccupying[c] or
        B.submarine.isOccupying[c]) => {
            c.x >= 0 and c.x <10
            c.y >= 10 and c.y <20
        }
    }
    --ships are of proper length and composed of ajacent coords
    all s: Ship | {
        #{c: Coordinate | s.isOccupying[c] = Yes} = s.length
        s.length > 1 => {
            all disj c1, c2: Coordinate | {
                (s.isOccupying[c1] and s.isOccupying[c2]) => {
                    (c1.x - c2.x < s.length and c1.y = c2.y) or
                    (c1.y - c2.y < s.length and c1.x = c2.x)
                }
            }
        }
    }
    --ships are not overlapping
    all disj s1, s2: Ship | {
        no c: Coordinate | {
            s1.isOccupying[c]
            s2.isOccupying[c]
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