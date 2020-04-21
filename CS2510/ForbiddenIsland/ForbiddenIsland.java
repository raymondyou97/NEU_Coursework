import java.util.*;
import tester.*;
import javalib.impworld.*;
import java.awt.Color;
import javalib.worldimages.*;

//Represents a single square of the game area
class Cell {
    // represents absolute height of this cell, in feet
    double height;
    // In logical coordinates, with the origin at the top-left corner of the scren
    int x;
    int y;
    // the four adjacent cells to this one
    Cell left;
    Cell top;
    Cell right;
    Cell bottom;
    // reports whether this cell is flooded or not
    boolean isFlooded;

    Cell(double height, int x, int y) {
        this.height = height;
        this.x = x;
        this.y = y; 
        this.isFlooded = false;
        this.left = this;
        this.right = this;
        this.top = this;
        this.bottom = this;
    }

    Cell(double height, int x, int y, boolean isFlooded) {
        this.height = height;
        this.x = x;
        this.y = y; 
        this.isFlooded = false;
        this.left = this;
        this.right = this;
        this.top = this;
        this.bottom = this;
    }

    //empty constructor
    Cell() {
        //allows creation of oceancell with just coordinates
    }

    //creates a colored cell:
    // - green to white for above sea
    // - blue to black for flooded 
    // - green to red for below sea level, but not flooded
    public WorldImage cellImage(int waterHeight) {
        int maxHeight = ForbiddenIslandWorld.ISLAND_SIZE / 2 + 2;
        double heightFromWater = this.height - waterHeight;
        if (heightFromWater < 0 - maxHeight) {
            heightFromWater = 0 - maxHeight;
        }

        double ratioOfHeight = heightFromWater / maxHeight;
        int r;
        int g;
        int b;
        int rZeroBase = 0;
        int gZeroBase = 0;
        int bZeroBase = 0;
        int remainderRBase = 255;
        int remainderGBase = 255;
        int remainderBBase = 255;

        //when land is above sea level
        if (ratioOfHeight > 0) {
            rZeroBase = 13;
            gZeroBase = 174;
            bZeroBase = 78;
            remainderRBase = 200 - rZeroBase;
            remainderGBase = 210 - gZeroBase;
            remainderBBase = 210 - bZeroBase;
        }
        //water only gets flooded when height is below 0
        else if (isFlooded) {
            rZeroBase = 0;
            gZeroBase = 0;
            bZeroBase = 0;
            ratioOfHeight = 1 - Math.abs(ratioOfHeight);
            remainderRBase = 0;
            remainderGBase = 0;
            remainderBBase = 205;
        }
        //when water is below sea level but not flooded
        else {

            ratioOfHeight = Math.abs(ratioOfHeight);
            rZeroBase = 80;
            gZeroBase = 100;
            bZeroBase = 78;
            remainderRBase = 140;
            remainderGBase = -100;
            remainderBBase = -78;

        }
        r = (int)((ratioOfHeight * remainderRBase) + rZeroBase);
        g = (int)((ratioOfHeight * remainderGBase) + gZeroBase);
        b = (int)((ratioOfHeight * remainderBBase) + bZeroBase);

        Color c = new Color(r, g, b);
        return new RectangleImage(11, 11, "solid", c);
    }
    
    //floods the current cell and recurses to the adjacent cells
    public void flood(int waterHeight) {
        if (this.height - waterHeight <= 0) {
            this.isFlooded = true;
            if (!this.top.isFlooded) {
                this.top.flood(waterHeight);
            }
            if (!this.left.isFlooded) {
                this.left.flood(waterHeight);
            }
            if (!this.right.isFlooded) {
                this.right.flood(waterHeight);
            }
            if (!this.bottom.isFlooded) {
                this.bottom.flood(waterHeight);
            }
        }
    }
}

class OceanCell extends Cell {
    OceanCell(int x, int y) {
        this.height = 0;
        this.x = x;
        this.y = y;
        this.isFlooded = true;
    }

    public WorldImage cellImage(int waterHeight) {
        return new RectangleImage(11, 11, "solid", 
                new Color(0, 0, 205));
    }
}

class Grid<T> {
    ArrayList<ArrayList<T>> grid;

    Grid() {
        this.grid = new ArrayList<ArrayList<T>>();
    }
    //flattens the grid into a list
    IList<T> flattenGrid() {
        IList<T> ret = new Empty<T>();

        for (ArrayList<T> row : this.grid) {
            for (T c : row) {
                ret = ret.add(c);
            }
        }
        return ret;
    }

}

//Represents the board containing all 0s
class ZeroGrid extends Grid<Double> {
    ZeroGrid() {
        ArrayList<ArrayList<Double>> grid = new ArrayList<ArrayList<Double>>();
        for (int y = 0; y <= ForbiddenIslandWorld.ISLAND_SIZE; y++) {
            grid.add(new ArrayList<Double>());
            for (int x = 0; x <= ForbiddenIslandWorld.ISLAND_SIZE; x++) {
                grid.get(y).add(0.0);
            }

        }
        this.grid = grid;
    }
}

//Represents the board with a mountain
class MountainGrid extends ZeroGrid {
    MountainGrid() {
        super();
        for (int y = 0; y <= ForbiddenIslandWorld.ISLAND_SIZE; y++) {
            int part1 = Math.abs(ForbiddenIslandWorld.ISLAND_SIZE / 2 - y);
            for (int x = 0; x <= ForbiddenIslandWorld.ISLAND_SIZE; x++) {
                int part2 =  Math.abs(ForbiddenIslandWorld.ISLAND_SIZE / 2 - x);
                int manhattanDistance = part1 + part2;

                this.grid.get(y).set(x, 
                        ForbiddenIslandWorld.ISLAND_SIZE / 2.0 + 1 - manhattanDistance);
            }

        }



    }
}

//represents the board with an island of random heights
class RandomMountainGrid extends ZeroGrid {
    RandomMountainGrid() {
        super();
        for (int y = 0; y <= ForbiddenIslandWorld.ISLAND_SIZE; y++) {
            int part1 = Math.abs(ForbiddenIslandWorld.ISLAND_SIZE / 2 - y);
            for (int x = 0; x <= ForbiddenIslandWorld.ISLAND_SIZE; x++) {
                int part2 =  Math.abs(ForbiddenIslandWorld.ISLAND_SIZE / 2 - x);
                int manhattanDistance = part1 + part2;
                if (ForbiddenIslandWorld.ISLAND_SIZE / 2.0 + 1 - manhattanDistance > 0) {
                    this.grid.get(y).set(x, 
                            Math.random() * (ForbiddenIslandWorld.ISLAND_SIZE / 2.0));
                }
                else {
                    this.grid.get(y).set(x, 
                            ForbiddenIslandWorld.ISLAND_SIZE / 2.0 + 1 - manhattanDistance);

                }
            }

        }

    }
}
//Grid for randomized terrain
class TerrainGrid extends ZeroGrid {
    TerrainGrid() {
        super();
        int max = ForbiddenIslandWorld.ISLAND_SIZE;
        int halfWay = (max / 2);
        this.grid.get(0).set(0, 0.0);
        this.grid.get(0).set(max, 0.0);
        this.grid.get(max).set(0, 0.0);
        this.grid.get(max).set(max, 0.0);

        this.grid.get(0).set(halfWay, 1.0);
        this.grid.get(halfWay).set(0, 1.0);
        this.grid.get(halfWay).set(max, 1.0);
        this.grid.get(max).set(halfWay, 1.0);

        this.grid.get(halfWay).set(halfWay, max / 2.0);


        //bottom right grid
        generateRandom(this.grid, halfWay, halfWay, max, max, true);
        //top right grid
        generateRandom(this.grid, halfWay, 0, max, halfWay, true);
        //bottom left grid
        generateRandom(this.grid, 0, halfWay, halfWay, max, true);
        //top left grid
        generateRandom(this.grid, 0, 0, halfWay, halfWay, true);


    }
    
    //generates the random terrain
    public void generateRandom(ArrayList<ArrayList<Double>> g,  
            int tlx, int tly, int brx, int bry, boolean recurse) {
        if (!recurse) {
            return;
        }
        double tl = g.get(tly).get(tlx);
        double tr = g.get(tly).get(brx);
        double bl = g.get(bry).get(tlx);
        double br = g.get(bry).get(brx);
        int midX = (tlx + brx) / 2;
        int midY = (tly + bry) / 2;

        int area = Math.abs(tlx - brx) * Math.abs(tly - bry);

        double top =  (Math.random() - .55) * Math.sqrt(area / .5) + (tl + tr) / 2;

        double left = (Math.random() - .55) * Math.sqrt(area / .5) + (tl + bl) / 2;

        double right = (Math.random() - .55) * Math.sqrt(area / .5) + (tr + br) / 2;

        double bottom = (Math.random() - .55) * Math.sqrt(area / .5) + (bl + br) / 2;

        double middle = (Math.random() - .55) * Math.sqrt(area / .5) + (tl + tr + bl + br) / 4;

        //Top
        g.get(tly).set(midX, top);
        //Left
        g.get(midY).set(tlx, left);
        //Right
        //g.get(midY).set(brx, right);
        //Bottom
        //g.get(bry).set(midX, bottom);
        //Middle
        g.get(midY).set(midX, middle);

        if (Math.abs(tlx - midX) < 2) {
            recurse = false;
        }

        //recursion on the bottom right rect
        this.generateRandom(g, midX, midY, brx, bry, recurse);
        //recursion on the top right rect
        this.generateRandom(g, midX, tly, brx, midY, recurse);
        //recursion on the bottom left rect
        this.generateRandom(g, tlx, midY, midX, bry, recurse);
        //recursion on the top left rect
        this.generateRandom(g, tlx, tly, midX, midY, recurse);



    }

}
//Represents the Board with cells

class CellGrid extends Grid<Cell> {
    //Takes in a grid of doubles to represent height of cells
    CellGrid(Grid<Double> board) {
        ArrayList<ArrayList<Cell>> cellBoard = new ArrayList<ArrayList<Cell>>();
        for (int y = 0; y < board.grid.size(); y++) {
            cellBoard.add(new ArrayList<Cell>());
            for (int x = 0; x < board.grid.get(y).size(); x++) {
                if (board.grid.get(y).get(x) <= 0) {
                    cellBoard.get(y).add(new OceanCell(x, y));
                }
                else {
                    cellBoard.get(y).add(new Cell(board.grid.get(y).get(x),
                            x, y));
                }
            }
        }

        for (int y = 0; y < cellBoard.size(); y++) {
            for (int x = 0; x < cellBoard.get(y).size(); x++) {
                if (y == 0) {
                    cellBoard.get(y).get(x).top = cellBoard.get(y).get(x);
                    cellBoard.get(y).get(x).bottom = cellBoard.get(y + 1).get(x);
                }
                else if (y == cellBoard.size() - 1) {
                    cellBoard.get(y).get(x).top = cellBoard.get(y - 1).get(x);
                    cellBoard.get(y).get(x).bottom = cellBoard.get(y).get(x);
                }
                else {
                    cellBoard.get(y).get(x).top = cellBoard.get(y - 1).get(x);
                    cellBoard.get(y).get(x).bottom = 
                            cellBoard.get(y + 1).get(x);                    
                }
                if (x == 0) {
                    cellBoard.get(y).get(x).left = cellBoard.get(y).get(x);
                    cellBoard.get(y).get(x).right = cellBoard.get(y).get(x + 1);
                }
                else if (x == cellBoard.size() - 1) {
                    cellBoard.get(y).get(x).left = cellBoard.get(y).get(x - 1);
                    cellBoard.get(y).get(x).right = cellBoard.get(y).get(x);
                }
                else {
                    cellBoard.get(y).get(x).left = cellBoard.get(y).get(x - 1);
                    cellBoard.get(y).get(x).right = cellBoard.get(y).get(x + 1);
                }
            }
        }
        this.grid = cellBoard;

    }
}
class Player {
    int x; //x coord
    int y; //y coord
    Cell on; //cell that this player in on
    boolean suitOn; //tells if player is wearing scuba suit
    boolean hasSuit; //tells if player has the suit

    Player(int x, int y, Cell on) {
        this.x = x;
        this.y = y;
        this.on = on;
        this.suitOn = false;
        this.hasSuit = false;
    }
    
    //returns the picture of the pilot
    public WorldImage playerImage() {
        return new FromFileImage("pilot-icon.png");
    }

    //checks if the player can move
    public boolean canMove(IList<Cell> board, String dir) {
        boolean ret = true;
        if (dir.equals("up") && this.on.top.isFlooded ||
                dir.equals("left") && this.on.left.isFlooded ||
                dir.equals("right") && this.on.right.isFlooded ||
                dir.equals("down") && this.on.bottom.isFlooded) {

            ret = false;
        }
        if (suitOn) {
            ret = true;
        }
        return ret;
    }

}
//represents the scubasuit the player can pick up
class ScubaSuit {
    int x;
    int y;

    ScubaSuit(int x, int y) {
        this.x = x;
        this.y = y;
    }
    
    //returns the picture of the scuba suit
    public WorldImage scubaImage() {
        return new FromFileImage("scuba-suit.png");
    }


}
class Target {
    int x; //x coord
    int y; //y coord

    Target(int x, int y) {
        this.x = x;
        this.y = y;
    }
    //returns the image of the gear
    public WorldImage targetImage() {
        return new FromFileImage("part.png");
    }

    //A Target can be removed regardless of situation
    public boolean canRemove(ArrayList<Target> piecesLeft) {
        return true;
    }
}
class HelicopterTarget extends Target {
    HelicopterTarget(int x, int y) {
        super(x, y);
    }
    //returns the image of the helicopter
    public WorldImage targetImage() {
        return new FromFileImage("helicopter.png");
    }
    //A HelicoperTarget can only be removed if it is the last targer
    public boolean canRemove(ArrayList<Target> piecesLeft) {
        return false;
    }
}

class ForbiddenIslandWorld extends World {
    // All the cells of the game, including the ocean
    IList<Cell> board;

    // the current height of the ocean
    int waterHeight;

    // the player
    Player player;
    //player 2
    Player player2;
    // the list of targets left
    ArrayList<Target> piecesLeft;
    //the list of targets obtained
    ArrayList<Target> piecesGathered;
    //The amount of time that has passed
    int timer;
    //Amount of steps taken by player 1
    int steps;
    //Amount of steps taken by player 2
    int steps2;
    //The scuba suit
    ScubaSuit suit;
    //time left on suit
    int suitTimeLeft;
    //highest height
    int timeLeft;


    // Defines an int constant
    static final int ISLAND_SIZE = 64;
    // Defines an int constant
    static final int GRID_SIZE = 11;

    ForbiddenIslandWorld(IList<Cell> board, int waterHeight) {
        this.board = board;
        this.waterHeight = waterHeight;

        this.player = new Player(ISLAND_SIZE / 2 + 1, ISLAND_SIZE / 2, new Cell());

        this.player2 = new Player(ISLAND_SIZE / 2 - 1, ISLAND_SIZE / 2, new Cell());

        this.piecesLeft = new ArrayList<Target>();
        this.piecesGathered = new ArrayList<Target>();
        this.timer = 1;
        this.steps = 0;

        //gets list of nonflooded spaces for future use
        ArrayList<Cell> nonFlooded = new ArrayList<Cell>();
        for (Cell c : board) {
            if (!c.isFlooded) {
                nonFlooded.add(c);
            }
            if (c.x == player.x && c.y == player.y) {
                player.on = c;
            }
            if (c.x == player2.x && c.y == player2.y) {
                player2.on = c;
            }
        }

        //places 4 pieces randomly on the board
        for (int i = 0; i < 4; i++) {
            int index = (int) (Math.random() * (nonFlooded.size() - 1));
            Cell c = nonFlooded.get(index);
            piecesLeft.add(new Target(c.x, c.y));
        }

        Cell max = new Cell(0, 0 , 0);
        for (Cell c : board) {
            if (c.height > max.height) {
                max = c;
            }
        }
        this.timeLeft = (int) max.height * 10;
        piecesLeft.add(new HelicopterTarget(max.x, max.y));

        //places the suit on the board
        int index = (int) (Math.random() * (nonFlooded.size() - 1));
        Cell c = nonFlooded.get(index);
        this.suit = new ScubaSuit(c.x, c.y);

        this.suitTimeLeft = 0;

    }
    ForbiddenIslandWorld() {
        //creates and empty world to run methods
    }


    //converts grid size to pixels
    int gridToPixel(int i) {
        return ForbiddenIslandWorld.GRID_SIZE * (i) + (ForbiddenIslandWorld.GRID_SIZE + 1) / 2;
    }

    //makes the scene
    public WorldScene makeScene() {
        WorldScene image = this.getEmptyScene();
        //makes the scene
        for (Cell c: board) {
            image.placeImageXY(c.cellImage(this.waterHeight), 
                    this.gridToPixel(c.x), this.gridToPixel(c.y));
        }
        //places pieces on scene
        for (Target t: this.piecesLeft) {
            image.placeImageXY(t.targetImage(), 
                    this.gridToPixel(t.x), this.gridToPixel(t.y));
        }
        //places scuba suit on scene
        image.placeImageXY(this.suit.scubaImage(),
                this.gridToPixel(this.suit.x), this.gridToPixel(this.suit.y));

        //places player on scene
        image.placeImageXY(this.player.playerImage(), 
                this.gridToPixel(this.player.x), this.gridToPixel(this.player.y));

        //places player2 on scene
        image.placeImageXY(this.player2.playerImage(), 
                this.gridToPixel(this.player2.x), this.gridToPixel(this.player2.y));

        //places the time left on scene
        String countdown = "Time Left: ";
        countdown = countdown + this.timeLeft / 60 + ":";
        if (this.timeLeft % 60 < 10) {
            countdown = countdown + 0;
        }
        countdown = countdown + this.timeLeft % 60;

        image.placeImageXY(
                new TextImage(countdown, 20 , Color.red), 
                this.gridToPixel(7), 
                this.gridToPixel(1));

        //places the timer on scene
        String clock = "";
        clock = clock + this.timer / 60 + ":";
        if (this.timer % 60 < 10) {
            clock = clock + 0;
        }
        clock = clock + this.timer % 60;

        image.placeImageXY(
                new TextImage(clock, 20 , Color.red), 
                this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE - 2), 
                this.gridToPixel(1));

        //places the time left on suit on screen

        String suitClock = "Time Left with Scuba Suit: " + 0 + ":";
        if (this.suitTimeLeft < 10) {
            suitClock = suitClock + "0";
        }
        suitClock = suitClock + suitTimeLeft;

        image.placeImageXY(
                new TextImage(suitClock, 20 , Color.red), 
                this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE / 2), 
                this.gridToPixel(1));


        //places p1 score

        String p1Score = "Player 1 Score: " + this.steps;


        image.placeImageXY(
                new TextImage(p1Score, 20 , Color.RED), 
                this.gridToPixel(8), 
                this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE - 1));

        //places p2 score

        String p2Score = "Player 2 Score: " + this.steps2;


        image.placeImageXY(
                new TextImage(p2Score, 20 , Color.RED), 
                this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE - 9), 
                this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE - 1));
        //return image
        return image;
    }
    
    //works every tick
    public void onTick() {
        if (timer % 10 == 0) {
            ArrayList<Cell> coastline = new ArrayList<Cell>();
            this.waterHeight++;
            for (Cell c: this.board) {

                if (!c.isFlooded && (c.top.isFlooded || c.right.isFlooded
                        || c.left.isFlooded || c.bottom.isFlooded)) {
                    coastline.add(c);
                }
            }

            for (Cell coast: coastline) {
                coast.flood(this.waterHeight);
            }


        }

        if (suitTimeLeft > 0) {
            suitTimeLeft--;
        }
        else {
            this.player.suitOn = false;
            this.player2.suitOn = false;
        }

        this.timer++;
        this.timeLeft--;

    }
    //works everytime a key is pressed
    // - directional keys move the player
    public void onKeyEvent(String ke) {
        if (ke.equals("up") && this.player.canMove(this.board, "up")) {
            this.player.x = this.player.on.top.x;
            this.player.y = this.player.on.top.y;
            this.player.on = this.player.on.top;
            this.steps++;
        }
        else if (ke.equals("left") && this.player.canMove(this.board, "left")) {
            this.player.x = this.player.on.left.x;
            this.player.y = this.player.on.left.y;
            this.player.on = this.player.on.left;
            this.steps++;

        }
        else if (ke.equals("down") && this.player.canMove(this.board, "down")) {
            this.player.x = this.player.on.bottom.x;
            this.player.y = this.player.on.bottom.y;
            this.player.on = this.player.on.bottom;
            this.steps++;
        }
        else if (ke.equals("right") && this.player.canMove(this.board, "right")) {
            this.player.x = this.player.on.right.x;
            this.player.y = this.player.on.right.y;
            this.player.on = this.player.on.right;
            this.steps++;
        }
        else if (ke.equals("w") && this.player2.canMove(this.board, "up")) {
            this.player2.x = this.player2.on.top.x;
            this.player2.y = this.player2.on.top.y;
            this.player2.on = this.player2.on.top;
            this.steps2++;
        }
        else if (ke.equals("a") && this.player2.canMove(this.board, "left")) {
            this.player2.x = this.player2.on.left.x;
            this.player2.y = this.player2.on.left.y;
            this.player2.on = this.player2.on.left;
            this.steps2++;

        }
        else if (ke.equals("s") && this.player2.canMove(this.board, "down")) {
            this.player2.x = this.player2.on.bottom.x;
            this.player2.y = this.player2.on.bottom.y;
            this.player2.on = this.player2.on.bottom;
            this.steps2++;
        }
        else if (ke.equals("d") && this.player2.canMove(this.board, "right")) {
            this.player2.x = this.player2.on.right.x;
            this.player2.y = this.player2.on.right.y;
            this.player2.on = this.player2.on.right;
            this.steps2++;
        }
        else if (ke.equals("m")) {
            ForbiddenIslandWorld reset = new ForbiddenIslandWorld(new CellGrid(
                    new MountainGrid()).flattenGrid(), 0);
            this.board = reset.board;
            this.piecesLeft = reset.piecesLeft;
            this.waterHeight = reset.waterHeight;
            this.piecesGathered = reset.piecesGathered;
            this.timer = reset.timer;
            this.player = reset.player;
            this.suit = reset.suit;
            this.suitTimeLeft = reset.suitTimeLeft;
            this.steps = reset.steps;
            this.steps2 = reset.steps2;
            this.timeLeft = reset.timeLeft;
            this.player2 = reset.player2;
        }
        else if (ke.equals("r")) {
            ForbiddenIslandWorld reset = new ForbiddenIslandWorld(new CellGrid(
                    new RandomMountainGrid()).flattenGrid(), 0);
            this.board = reset.board;
            this.piecesLeft = reset.piecesLeft;
            this.waterHeight = reset.waterHeight;
            this.piecesGathered = reset.piecesGathered;
            this.timer = reset.timer;
            this.player = reset.player;
            this.suit = reset.suit;
            this.suitTimeLeft = reset.suitTimeLeft;
            this.steps = reset.steps;
            this.steps2 = reset.steps2;
            this.timeLeft = reset.timeLeft;
            this.player2 = reset.player2;
        }
        else if (ke.equals("t")) {
            ForbiddenIslandWorld reset = new ForbiddenIslandWorld(new CellGrid(
                    new TerrainGrid()).flattenGrid(), 0);
            this.board = reset.board;
            this.piecesLeft = reset.piecesLeft;
            this.waterHeight = reset.waterHeight;
            this.piecesGathered = reset.piecesGathered;
            this.timer = reset.timer;
            this.player = reset.player;
            this.suit = reset.suit;
            this.suitTimeLeft = reset.suitTimeLeft;
            this.steps = reset.steps;
            this.steps2 = reset.steps2;
            this.timeLeft = reset.timeLeft;
            this.player2 = reset.player2;
        }
        else if (ke.equals("y")) {
            if (this.player.hasSuit) {
                this.player.suitOn = true;
                this.suitTimeLeft = 20;
                this.player.hasSuit = false;
            }
            if (this.player2.hasSuit) {
                this.player2.suitOn = true;
                this.suitTimeLeft = 20;
                this.player2.hasSuit = false;
            }
        }
        //collects the pieces
        Target p = new Target(0, 0);
        for (Target piece: this.piecesLeft) {
            if (piece.canRemove(this.piecesLeft) && 
                    (piece.x == this.player.x && piece.y == this.player.y ||
                    piece.x == this.player2.x && piece.y == this.player2.y)) {
                this.piecesGathered.add(piece);
                p = piece;
            }
        }

        piecesLeft.remove(p);

        //collects the scuba suit
        if (suit.x == player.x && suit.y == player.y) {
            player.hasSuit = true;
            //moves the suit off the screen
            suit.x = -20;
            suit.y = -20;

        }
        if (suit.x == player2.x && suit.y == player2.y) {
            player2.hasSuit = true;
            //moves the suit off the screen
            suit.x = -20;
            suit.y = -20;
        }
    }

    //Ends the game if:
    // - both players are on helicopter and there are no more other pieces
    // - one of the 2 players drown
    public WorldEnd worldEnds() {
        if (this.piecesLeft.size() == 1 &&
                this.player.x == piecesLeft.get(0).x && this.player.y == piecesLeft.get(0).y &&
                this.player2.x == piecesLeft.get(0).x && this.player2.y == piecesLeft.get(0).y) {
            WorldScene winScreen = this.makeScene();
            winScreen.placeImageXY(
                    new TextImage("You've Escaped", 70, Color.red), 
                    this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE / 2), 
                    this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE / 2));
            return new WorldEnd(true, winScreen);
        }
        else if (this.player.on.isFlooded && !player.suitOn ||
                this.player2.on.isFlooded && !player2.suitOn) {
            WorldScene winScreen = this.makeScene();
            winScreen.placeImageXY(
                    new TextImage("You have drowned", 70, Color.red), 
                    this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE / 2), 
                    this.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE / 2));
            return new WorldEnd(true, winScreen);
        }
        else {
            return new WorldEnd(false, this.makeScene());
        }

    }

}


class IListIterator<T> implements Iterator<T> {
    IList<T> items;

    IListIterator(IList<T> items) {
        this.items = items;
    }
    //checks if there is a next value  
    public boolean hasNext() {
        return items.isCons();
    }
    // Get the next value in this sequence
    // EFFECT: Advance the iterator to the subsequent value
    public T next() {
        Cons<T> listAsCons = this.items.asCons();
        T answer = listAsCons.first;
        this.items = listAsCons.rest;
        return answer;
    }
    //Don't remove
    public void remove() {
        throw new UnsupportedOperationException("Don't do this!");
    }

}

interface IList<T> extends Iterable<T> {
    //adds and element to the end of the list
    IList<T> add(T item);
    //returns whether the list is a Cons
    boolean isCons();
    //returns the list as a Cons
    Cons<T> asCons();

}

class Cons<T> implements IList<T> {
    T first;
    IList<T> rest;

    Cons(T first, IList<T> rest) {
        this.first = first;
        this.rest = rest;
    }
    //returns the iterator
    public Iterator<T> iterator() {
        return new IListIterator<T>(this);
    }
    //adds an element to the end of the list
    public IList<T> add(T item) {
        return new Cons<T>(this.first, this.rest.add(item));
    }
    //returns true
    public boolean isCons() {
        return true;
    }
    //returns the list as a Cons
    public Cons<T> asCons() {
        return this;
    }

}

class Empty<T> implements IList<T> {
    Empty(){
        //represents empty list
    }
    //returns the iterator
    public Iterator<T> iterator() {
        return new IListIterator<T>(this);
    }
    //adds an element to the end of the list
    public IList<T> add(T item) {
        return new Cons<T>(item, new Empty<T>());
    }
    //returns false
    public boolean isCons() {
        return false;
    }
    //returns the list as a Cons
    public Cons<T> asCons() {
        throw new RuntimeException("Not a Cons");
    }

}



class ExamplesForbiddenIslandWorld {
    ForbiddenIslandWorld pre = new ForbiddenIslandWorld();
    IList<Cell> mountain;
    IList<Cell> randomMountain;
    //examples of cells
    Cell c0 = new Cell();
    Cell c1 = new Cell(2, 3, 4);
    Cell c2 = new Cell(-3, -6, -1);
    Cell c3 = new Cell(6, 2, 3, false);
    Cell c4 = new Cell(-5, 2, 3, true);
    Cell c5 = new OceanCell(2, 3);
    Cell c7 = new Cell(1, 0, 0, false);
    Cell c8 = new Cell(1, 0, 1, true);
    Cell c9 = new Cell(1, 1, 0, true);
    Cell c10  = new Cell(100, 0, 0, false);
    Cell c11 = new Cell(100, 0, 1, true);
    Cell c12 = new Cell(100, 1, 0, true);
    Cell c13 = new Cell(100, 0, 0, false);
    Cell c14 = new Cell(100, 0, 1, true);
    Cell c15 = new Cell(100, 1, 0, true);
    Cell c16 = new Cell(100, 1, 1, true);

    boolean testCellImage(Tester t) {
        return t.checkExpect(c0.cellImage(0), new RectangleImage(11, 11, "solid", 
                new Color(80, 100, 78))) &&
                t.checkExpect(c0.cellImage(50), new RectangleImage(11, 11, "solid", 
                        new Color(220, 0, 0))) &&
                t.checkExpect(c0.cellImage(-30), new RectangleImage(11, 11, "solid", 
                        new Color(178, 205, 194))) &&
                t.checkExpect(c1.cellImage(0), new RectangleImage(11, 11, "solid", 
                        new Color(24, 176, 85))) &&
                t.checkExpect(c1.cellImage(5), new RectangleImage(11, 11, "solid", 
                        new Color(92, 91, 71))) &&
                t.checkExpect(c1.cellImage(-12), new RectangleImage(11, 11, "solid", 
                        new Color(90, 188, 132))) &&
                t.checkExpect(c2.cellImage(0), new RectangleImage(11, 11, "solid", 
                        new Color(92, 91, 71))) &&
                t.checkExpect(c2.cellImage(40), new RectangleImage(11, 11, "solid", 
                        new Color(220, 0, 0))) &&
                t.checkExpect(c2.cellImage(-20), new RectangleImage(11, 11, "solid", 
                        new Color(106, 192, 144))) &&
                t.checkExpect(c3.cellImage(0), new RectangleImage(11, 11, "solid", 
                        new Color(46, 180, 101))) &&
                t.checkExpect(c3.cellImage(60), new RectangleImage(11, 11, "solid", 
                        new Color(220, 0, 0))) &&
                t.checkExpect(c3.cellImage(-20), new RectangleImage(11, 11, "solid", 
                        new Color(156, 201, 178))) &&
                t.checkExpect(c4.cellImage(0), new RectangleImage(11, 11, "solid", 
                        new Color(100, 85, 66))) &&
                t.checkExpect(c4.cellImage(20), new RectangleImage(11, 11, "solid", 
                        new Color(182, 26, 20))) &&
                t.checkExpect(c4.cellImage(-20), new RectangleImage(11, 11, "solid", 
                        new Color(95, 189, 136))) &&
                t.checkExpect(c5.cellImage(-20), new RectangleImage(11, 11, "solid", 
                        new Color(0, 0, 205))) &&
                t.checkExpect(c5.cellImage(-0), new RectangleImage(11, 11, "solid", 
                        new Color(0, 0, 205)));

    }

    Cell flood1;
    Cell flood2;
    Cell flood3;
    Cell flood4;
    Cell flood5;
    Cell flood6;
    Cell flood7;
    Cell flood8;
    Cell flood9;
    Cell flood10;

    void initFlood() {
        flood1 = new Cell(1, 1, 1, false);
        flood2 = new Cell(10, 1, 1, false);
        flood3 = new Cell(10, 1, 1, false);
        flood4 = new Cell(10, 1, 1, false);
        flood5 = new Cell(10, 1, 1, false);
        flood6 = new Cell(1, 1, 1, true);
        flood7 = new Cell(10, 1, 1, true);
        flood8 = new Cell(10, 1, 1, true);
        flood9 = new Cell(10, 1, 1, true);
        flood10 = new Cell(10, 1, 1, true);

    }
    void testFlood(Tester t) {
        this.initFlood();
        flood1.left = flood2;
        flood1.top = flood3;
        flood1.right = flood4;
        flood1.bottom = flood5;
        flood1.flood(5);
        t.checkExpect(flood1.isFlooded, true);
        flood1.isFlooded = false;
        flood2.left = flood2;
        flood2.right = flood1;
        flood2.flood(1500);
        flood3.bottom = flood1;
        flood4.left = flood1;
        flood5.top = flood1;
        t.checkExpect(flood2.isFlooded, true);
        t.checkExpect(flood3.isFlooded, true);
        t.checkExpect(flood4.isFlooded, true);
        t.checkExpect(flood5.isFlooded, true);
        flood6.flood(5);
        t.checkExpect(flood6.isFlooded, true);
        flood7.isFlooded = false;
        t.checkExpect(flood7.isFlooded, false);

    }
    Player P1 = new Player(2, 2, c1);
    Player P2 = new Player(0, 0, c0);
    Player P3 = new Player(100, 100, c5);
    boolean playerImage(Tester t) {
        return t.checkExpect(P1.playerImage(), new FromFileImage("pilot-icon.png")) &&
                t.checkExpect(P2.playerImage(), new FromFileImage("pilot-icon.png")) &&
                t.checkExpect(P3.playerImage(), new FromFileImage("pilot-icon.png"));

    }


    Cell canMove1;
    Cell canMove2;
    Cell canMove3;
    Cell canMove4;
    Cell canMove5;

    boolean canMove(Tester t) {
        c7.bottom = c8;
        c7.right = c9;
        c7.left = c7;
        c7.top = c7;
        return t.checkExpect(P1.canMove(mtCellList, "up"), true) &&
                t.checkExpect(P1.canMove(mtCellList, "down"), true) &&
                t.checkExpect(P1.canMove(mtCellList, "left"), true) &&
                t.checkExpect(P1.canMove(mtCellList, "right"), true) &
                t.checkExpect(P1.canMove(consList1, "up"), true) &&
                t.checkExpect(P1.canMove(consList1, "down"), true) &&
                t.checkExpect(P1.canMove(consList1, "left"), true) &&
                t.checkExpect(P1.canMove(consList1, "right"), true) &&
                t.checkExpect(P1.canMove(consList2, "up"), true) &&
                t.checkExpect(P2.canMove(consList2, "right"), false) &&
                t.checkExpect(P2.canMove(consList2, "top"), false) &&
                t.checkExpect(P2.canMove(consList2, "left"), false) &&
                t.checkExpect(P2.canMove(consList2, "bottom"), false) &&
                t.checkExpect(P3.canMove(consList2, "up"), true) &&
                t.checkExpect(P3.canMove(consList2, "right"), false) &&
                t.checkExpect(P3.canMove(consList2, "top"), false) &&
                t.checkExpect(P3.canMove(consList2, "left"), false) &&
                t.checkExpect(P3.canMove(consList2, "bottom"), false);
    }
    IList<Cell> mtCellList = new Empty<Cell>();
    IList<Cell> consList1 = new Cons<Cell>(c1, new Cons<Cell>(c2, 
            new Cons<Cell>(c3, new Empty<Cell>())));
    IList<Cell> consList2 = new Cons<Cell>(c7, new Cons<Cell>(c9, 
            new Cons<Cell>(c9, new Empty<Cell>())));
    IList<Cell> consList3 = new Cons<Cell>(c10, new Cons<Cell>(c11, 
            new Cons<Cell>(c12, new Cons<Cell>(c13, new Cons<Cell>(c14, 
                    new Cons<Cell>(c15, new Empty<Cell>()))))));

    ArrayList<ArrayList<Cell>> test = new ArrayList<ArrayList<Cell>>();
    void testNestedList() {
        test.add(new ArrayList<Cell>());
        test.add(new ArrayList<Cell>());
        test.get(0).add(new Cell(0, 0, 0));
        test.get(0).add(new Cell(0, 1, 0));
        test.get(1).add(new Cell(0, 0, 1));
        test.get(1).add(new Cell(0, 1, 1));
    }


    //examples of Grids
    Grid<Double> emptyGrid = new ZeroGrid();
    Grid<Double> mountGrid = new MountainGrid();
    Grid<Double> randMountGrid = new RandomMountainGrid();
    Grid<Cell> cellMountGrid = new CellGrid(mountGrid);
    ArrayList<ArrayList<Double>>  nestList1 = new ArrayList<ArrayList<Double>>();
    ArrayList<ArrayList<Double>>  nestList2 = new ArrayList<ArrayList<Double>>();

    Grid<Double> testGrid = new Grid<Double>();
    Grid<Double> testGrid2 = new Grid<Double>();
    Grid<Double> testGrid3 = new Grid<Double>();

    void makeTestGrids() {
        nestList1.add(new ArrayList<Double>());
        nestList1.add(new ArrayList<Double>());
        nestList1.get(0).add(1.0);
        nestList1.get(0).add(2.0);
        nestList1.get(1).add(1.0);
        nestList1.get(1).add(2.0);
        testGrid.grid = nestList1;
        nestList2.add(new ArrayList<Double>());
        nestList2.add(new ArrayList<Double>());
        nestList2.get(0).add(0.0);
        nestList2.get(0).add(1.0);
        nestList2.get(0).add(2.0);
        nestList2.get(1).add(0.0);
        nestList2.get(1).add(1.0);
        nestList2.get(1).add(2.0);
        testGrid3.grid = nestList2;
    }
    //tests FlattenGrid method for ForbiddenIslandWorlds
    boolean testFlattenGrid(Tester t) {
        this.makeTestGrids();
        return t.checkExpect(testGrid.flattenGrid(), new Cons<Double>(1.0, 
                new Cons<Double>(2.0, 
                        new Cons<Double>(1.0, 
                                new Cons<Double>(2.0, new Empty<Double>()))))) &&
                t.checkExpect(testGrid2.flattenGrid(), new Empty<Double>()) &&
                t.checkExpect(testGrid3.flattenGrid(), new Cons<Double>(0.0, 
                        new Cons<Double>(1.0, 
                                new Cons<Double>(2.0, 
                                        new Cons<Double>(0.0, new Cons<Double>(1.0, 
                                                new Cons<Double>(2.0, new Empty<Double>())))))));
    }  

    //tests the gridToPixel method for World
    boolean testGridToPixel(Tester t) {
        return t.checkExpect(pre.gridToPixel(0), 6) &&
                t.checkExpect(pre.gridToPixel(5), 61) &&
                t.checkExpect(pre.gridToPixel(-2), -16);
    }

    ForbiddenIslandWorld world3;
    ForbiddenIslandWorld world4;
    void initOnTick() {
        world3 = new ForbiddenIslandWorld(consList3, 100);
        world3.timer = 100;
        world3.steps = 50;
        world3.steps2 = 60;
        world3.suit = s1;
        world3.suitTimeLeft = 10;
        world3.timeLeft = 1000;
    }
    void OnTick(Tester t) {
        this.initOnTick();
        world3.onTick();
        t.checkExpect(world3.timer, 101);
        t.checkExpect(world3.timeLeft, 999);
        t.checkExpect(world3.suitTimeLeft, 9);
        t.checkExpect(world.suit, s1);

    }

    void initOnKeyEvent() {
        world4 = new ForbiddenIslandWorld(consList3, 0);
        world4.player = new Player(0, 0, c10);
        world4.player2 = new Player(0, 1, c11);

    }
    void testOnKeEvent(Tester t) {
        this.initOnKeyEvent();
        c10.right = c12;
        c12.bottom = c16;
        c11.left = c10;
        //test player 1 movement
        world4.onKeyEvent("up");
        t.checkExpect(world4.player.x, 0);
        t.checkExpect(world4.player.y, 0);
        world4.onKeyEvent("left");
        t.checkExpect(world4.player.x, 0);
        t.checkExpect(world4.player.y, 0);
        world4.onKeyEvent("right");
        t.checkExpect(world4.player.x, 1);
        t.checkExpect(world4.player.y, 0);
        world4.onKeyEvent("down");
        t.checkExpect(world4.player.x, 1);
        t.checkExpect(world4.player.y, 1);


        //test player 2 movement
        world4.onKeyEvent("a");
        t.checkExpect(world4.player2.x, 0);
        t.checkExpect(world4.player2.y, 0);
        world4.onKeyEvent("w");
        t.checkExpect(world4.player2.x, 0);
        t.checkExpect(world4.player2.y, 0);
        world4.onKeyEvent("d");
        t.checkExpect(world4.player2.x, 1);
        t.checkExpect(world4.player2.y, 0);
        world4.onKeyEvent("s");
        t.checkExpect(world4.player2.x, 1);
        t.checkExpect(world4.player2.y, 1);




    }

    IList<Integer> empty = new Empty<Integer>();
    IList<Integer> list1 = new Cons<Integer>(5, new Empty<Integer>());

    IList<Integer> list2 = new Cons<Integer>(7, 
            new Cons<Integer>(4, 
                    new Cons<Integer>(3, 
                            new Cons<Integer>(2, empty))));
    IListIterator<Integer> it1 = new IListIterator<Integer>(empty);
    IListIterator<Integer> it2 = new IListIterator<Integer>(list1);
    IListIterator<Integer> it3 = new IListIterator<Integer>(list2);

    //Tests the hasNext method for IListIterator
    boolean testHasNext(Tester t) {
        return t.checkExpect(it1.hasNext(), false) &&
                t.checkExpect(new IListIterator<Integer>(new Cons<Integer>(5, 
                        new Empty<Integer>())).hasNext(), true) &&
                t.checkExpect(it3.hasNext(), true);
    }
    //Tests the hasNext method for IListIterator
    boolean testNext(Tester t) {
        return t.checkException(new RuntimeException("Not a Cons"), it1, "next") &&
                t.checkExpect(it2.next(), 5) &&
                t.checkExpect(it3.next(), 7);
    }

    //Tests the remove method for IListIterator
    boolean testRemove(Tester t) {
        return t.checkException(new UnsupportedOperationException("Don't do this!"), 
                it1, "remove") &&
                t.checkException(new UnsupportedOperationException("Don't do this!"), 
                        it2, "remove") &&
                t.checkException(new UnsupportedOperationException("Don't do this!"), 
                        it3, "remove");
    }

    //Tests the add method for ILists
    boolean testAdd(Tester t) {
        return t.checkExpect(empty.add(5), new Cons<Integer>(5, new Empty<Integer>())) &&
                t.checkExpect(list1.add(2), new Cons<Integer>(5, 
                        new Cons<Integer>(2, new Empty<Integer>()))) &&
                t.checkExpect(list2.add(10), new Cons<Integer>(7, 
                        new Cons<Integer>(4, 
                                new Cons<Integer>(3, 
                                        new Cons<Integer>(2, 
                                                new Cons<Integer>(10, 
                                                        new Empty<Integer>()))))));
    }
    //Tests the isCons method for ILists
    boolean testIsCons(Tester t) {
        return  t.checkExpect(empty.isCons(), false) &&
                t.checkExpect(list1.isCons(), true) &&
                t.checkExpect(list2.isCons(), true);
    }
    //Tests the asCons method for ILists
    boolean testAsCons(Tester t) {
        return t.checkException(new RuntimeException("Not a Cons"), empty, "asCons") &&
                t.checkExpect(list1.asCons(), list1) &&
                t.checkExpect(list2.asCons(), list2);
    }

    ScubaSuit s1 = new ScubaSuit(1, 1);
    ScubaSuit s2 = new ScubaSuit(0, 0);
    ScubaSuit s3 = new ScubaSuit(69, 69);
    ScubaSuit s4 = new ScubaSuit(420, 420);

    boolean testScubaImage(Tester t) {
        return t.checkExpect(s1.scubaImage(), new FromFileImage("scuba-suit.png")) &&
                t.checkExpect(s2.scubaImage(), new FromFileImage("scuba-suit.png")) &&
                t.checkExpect(s3.scubaImage(), new FromFileImage("scuba-suit.png")) &&
                t.checkExpect(s4.scubaImage(), new FromFileImage("scuba-suit.png"));
    }

    Target t1 = new Target(0, 0);
    Target t2 = new Target(1, 1);
    Target t3 = new Target(69, 69);
    Target t4 = new Target(420, 420);

    ArrayList<Target> alt = new ArrayList<Target>();

    boolean testTargetImage(Tester t) {
        return t.checkExpect(t1.targetImage(), new FromFileImage("part.png")) &&
                t.checkExpect(t2.targetImage(), new FromFileImage("part.png")) &&
                t.checkExpect(t3.targetImage(), new FromFileImage("part.png")) &&
                t.checkExpect(t4.targetImage(), new FromFileImage("part.png"));
    }

    boolean testCanRemove(Tester t) {
        alt.add(t1);
        alt.add(t2);
        alt.add(t3);
        alt.add(t4);
        alt.set(0, t3);
        return t.checkExpect(t1.canRemove(alt), true) &&
                t.checkExpect(t2.canRemove(alt), true) &&
                t.checkExpect(t3.canRemove(alt), true) &&
                t.checkExpect(t4.canRemove(alt), true) &&
                t.checkExpect(t3.canRemove(alt), true);


    }

    Target h1 = new HelicopterTarget(1, 1);
    Target h2 = new HelicopterTarget(0, 0);
    Target h3 = new HelicopterTarget(69, 69);
    Target h4 = new HelicopterTarget(420, 420);

    boolean testHelicopterTargetImage(Tester t) {
        return t.checkExpect(h1.targetImage(), new FromFileImage("helicopter.png")) &&
                t.checkExpect(h2.targetImage(), new FromFileImage("helicopter.png")) &&
                t.checkExpect(h3.targetImage(), new FromFileImage("helicopter.png")) &&
                t.checkExpect(h4.targetImage(), new FromFileImage("helicopter.png"));
    }
    boolean testHelicopterCanRemove(Tester t) {
        alt.add(t1);
        alt.add(t2);
        alt.add(t3);
        alt.add(t4);
        alt.set(0, t3);
        return t.checkExpect(t1.canRemove(alt), true) &&
                t.checkExpect(t2.canRemove(alt), true) &&
                t.checkExpect(t3.canRemove(alt), true) &&
                t.checkExpect(t4.canRemove(alt), true) &&
                t.checkExpect(t3.canRemove(alt), true);
    }

    ForbiddenIslandWorld world = new ForbiddenIslandWorld(consList3, 100);

    boolean testMakeScene(Tester t) {
        return t.checkExpect(world.makeScene().width, 0) &&
                t.checkExpect(world.makeScene().height, 0);
    }

}

class ForbiddenIslandWorldExamples {
    public static void main(String[] argv) {

        // run the tests - showing only the failed test results
        ExamplesForbiddenIslandWorld ex = new ExamplesForbiddenIslandWorld();
        Tester.runReport(ex, false, false);


        ForbiddenIslandWorld w = new ForbiddenIslandWorld(new CellGrid(
                new TerrainGrid()).flattenGrid(), 0);
        w.bigBang(ex.pre.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE) + 5, 
                ex.pre.gridToPixel(ForbiddenIslandWorld.ISLAND_SIZE) + 5, 1);


    }



}


