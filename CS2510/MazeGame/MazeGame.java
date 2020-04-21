import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Stack;
import tester.*;
import javalib.impworld.*;
import java.awt.Color;
import javalib.worldimages.*;

class Edge implements Comparable<Edge> {
    Cell connected1;
    Cell connected2;
    double weight;

    Edge() {
        //empty edge
    }

    Edge(Cell c1, Cell c2) {
        this.connected1 = c1;
        this.connected2 = c2;
        this.weight =  Math.floor(Math.random() * (MazeWorld.MAZE_WIDTH * MazeWorld.MAZE_HEIGHT));
    }

    public int compareTo(Edge c) {
        return (int)(this.weight - c.weight);
    }
    public WorldImage edgeImage(Color c) {
        int x1 = connected1.x * MazeWorld.CELL_WIDTH + MazeWorld.CELL_WIDTH / 2;
        int x2 = connected2.x * MazeWorld.CELL_WIDTH + MazeWorld.CELL_WIDTH / 2;
        int x = (x1 + x2) / 2; 

        int y1 = connected1.y * MazeWorld.CELL_HEIGHT + MazeWorld.CELL_HEIGHT / 2;
        int y2 = connected2.y * MazeWorld.CELL_HEIGHT + MazeWorld.CELL_HEIGHT / 2;
        int y = (y1 + y2) / 2;

        //either x == x1 or y == y1
        if (connected1 == connected2) {
            return new RectangleImage(MazeWorld.CELL_WIDTH - 2, MazeWorld.CELL_HEIGHT - 2, 
                    "Solid", c);
        }
        else if (x == x1) {
            return new RectangleImage(MazeWorld.CELL_WIDTH - 2, MazeWorld.CELL_HEIGHT * 2 - 2, 
                    "Solid", c);
        }
        else if (y == y1) {
            return new RectangleImage(MazeWorld.CELL_WIDTH * 2 - 2, MazeWorld.CELL_HEIGHT - 2, 
                    "Solid", c);
        }
        return new RectangleImage(0, 0, "Solid", c);
    }
    public WorldImage fixEdge(Color c) {
        int x1 = connected1.x * MazeWorld.CELL_WIDTH + MazeWorld.CELL_WIDTH / 2;
        int x2 = connected2.x * MazeWorld.CELL_WIDTH + MazeWorld.CELL_WIDTH / 2;
        int x = (x1 + x2) / 2; 

        int y1 = connected1.y * MazeWorld.CELL_HEIGHT + MazeWorld.CELL_HEIGHT / 2;
        int y2 = connected2.y * MazeWorld.CELL_HEIGHT + MazeWorld.CELL_HEIGHT / 2;
        int y = (y1 + y2) / 2;

        //either x == x1 or y == y1
        if (connected1 == connected2) {
            return new RectangleImage(MazeWorld.CELL_WIDTH - 2, MazeWorld.CELL_HEIGHT - 2, 
                    "Solid", c);
        }
        else if (x == x1) {
            return new RectangleImage(MazeWorld.CELL_WIDTH - 2, 4, 
                    "Solid", c);
        }
        else if (y == y1) {
            return new RectangleImage(4, MazeWorld.CELL_HEIGHT - 2, 
                    "Solid", c);
        }
        return new RectangleImage(0, 0, "Solid", c);
    }


}
class Cell {
    int x;
    int y;
    boolean beenSearched;


    Cell(int x, int y) {
        this.x = x;
        this.y = y;
        beenSearched = false;
    }


    //overrides the equal function in object
    public boolean equaloverride(Object o) {
        if (!(o instanceof Cell)) {
            return false;
        }
        Cell c = (Cell)o;
        return this.x == c.x && this.y == c.y; 
    }
    public WorldImage cellImage() {
        return new RectangleImage(MazeWorld.CELL_WIDTH, 
                MazeWorld.CELL_HEIGHT, "outline", Color.GRAY);
    }
    public int cellCode() {
        return x + y * MazeWorld.MAZE_WIDTH;
    }
}
class Player {
    Cell on;

    Player(Cell on) {
        this.on = on;
    }

    public WorldImage playerImage() {
        int radius;
        radius = Math.min(MazeWorld.CELL_WIDTH, MazeWorld.CELL_HEIGHT);
        radius -= 2;
        radius /= 2;
        return new CircleImage(radius, "Solid", Color.YELLOW);
    }

}

class MazeWorld extends World {
    // static values to change the world's width/height
    public static int MAZE_WIDTH = 25;
    public static int MAZE_HEIGHT = 15;
    public static Color BACKGROUND = new Color(212, 212, 212);
    public static int WORLD_WIDTH = 1000;
    public static int WORLD_HEIGHT = 600;
    public static int CELL_WIDTH = WORLD_WIDTH / MAZE_WIDTH;
    public static int CELL_HEIGHT = WORLD_HEIGHT / MAZE_HEIGHT;

    // for Kruskal’s Algorithm
    HashMap<Integer, Integer> representatives;
    ArrayList<Edge> worklist;

    // for the Searches
    HashMap<Integer, Edge> cameFromEdge;
    ArrayList<Cell> breadthList;
    Stack<Cell> depthList;

    //For display
    ArrayList<Edge> edgesInTree;
    ArrayList<Edge> path;
    ArrayList<Edge> pathEdges;
    ArrayList<Edge> fixEdges;

    Player player;



    // To tell which search to use
    boolean depth;
    boolean breadth;
    boolean manual;

    //Whistles
    //- toggle view
    boolean view;

    //Bells

    Cell entrance;
    Cell exit;


    MazeWorld() {


        //represents whether the world is currently doing:
        // - Depth First Search
        // - Breadth First Search
        // - Letting Player manually search
        depth = false;
        breadth = false;
        manual = false;
        view = true;



        representatives = new HashMap<Integer, Integer>();
        edgesInTree = new ArrayList<Edge>();
        worklist = new ArrayList<Edge>();
        CellGrid grid = new CellGrid();

        entrance = grid.grid.get(0).get(0);
        exit = grid.grid.get(grid.grid.size() - 1).get(grid.grid.get(0).size() - 1);
        //for searches
        cameFromEdge = new HashMap<Integer, Edge>();
        breadthList = new ArrayList<Cell>();
        depthList = new Stack<Cell>();

        depthList.push(grid.grid.get(0).get(0));
        breadthList.add(grid.grid.get(0).get(0));

        path = new ArrayList<Edge>();
        pathEdges = new ArrayList<Edge>();
        fixEdges = new ArrayList<Edge>();

        player = new Player(grid.grid.get(0).get(0));

        //creates the worklist
        int cellNum = 0;
        for (int y = 0; y < grid.grid.size(); y++) {
            for (int x = 0; x < grid.grid.get(y).size(); x++) {
                int top = y - 1;
                int bottom = y + 1;
                int left = x - 1;
                int right = x + 1;

                //accounts for edges of the grid
                if (y == 0) {
                    top++;
                }
                else if (y == grid.grid.size() - 1) {
                    bottom--;
                }
                if (x == 0) {
                    left++;
                }
                else if (x == grid.grid.get(y).size() - 1) {
                    right--;
                }
                Cell topCell = grid.grid.get(top).get(x);
                Cell bottomCell = grid.grid.get(bottom).get(x);
                Cell leftCell = grid.grid.get(y).get(left);
                Cell rightCell = grid.grid.get(y).get(right);
                Cell cell = grid.grid.get(y).get(x);

                //sets up the hashmap

                representatives.put(cellNum, cellNum);

                if (topCell != cell) {
                    worklist.add(new Edge(cell, topCell));
                }
                if (bottomCell != cell) {
                    worklist.add(new Edge(cell, bottomCell));
                }
                if (leftCell != cell) {
                    worklist.add(new Edge(cell, leftCell));
                }
                if (rightCell != cell) {
                    worklist.add(new Edge(cell, rightCell));
                }

                cellNum++;
            }
            Collections.sort(worklist);
        }
        this.algo();


    }

    public void algo() {
        while (worklist.size() > 0) {
            Edge currentEdge = this.worklist.get(0);
            int rep1 = currentEdge.connected1.cellCode();
            int rep2 = currentEdge.connected2.cellCode();

            if (this.find(this.representatives, 
                    rep1).equals(this.find(this.representatives, rep2))) {
                this.worklist.remove(0);
            }
            else {
                this.edgesInTree.add(currentEdge);

                this.union(this.representatives, this.find(this.representatives, rep1),
                        this.find(this.representatives, rep2));
                this.worklist.remove(0);
            }

        }
    }
    public <T> T find(HashMap<T, T> reps, T rep) {
        T value = reps.get(rep);
        if (rep.equals(value)) {
            return value;
        }
        else {
            return this.find(reps, value);
        }
    }
    public <T> void union(HashMap<T, T> reps, T rep1, T rep2) {
        //reps.remove(rep1);
        reps.put(rep1, rep2);
    }


    public ArrayList<Edge> breadthSearch(Cell target) {
        if (breadthList.size() > 0) {
            Cell next = breadthList.get(0);
            if (next.beenSearched) {
                breadthList.remove(0);
                return path;
            }
            else if (next.equaloverride(target)) {
                return reconstruct(cameFromEdge, next);
            }
            else {
                Edge displayEdge = new Edge(next, next);
                for (Edge e: edgesInTree) {
                    if (e.connected2.equaloverride(next) && !e.connected1.beenSearched) {
                        breadthList.add(e.connected1);
                        cameFromEdge.put(e.connected1.cellCode(), new Edge(next, e.connected1));
                        displayEdge = e;
                        fixEdges.add(e);
                        //pathEdges.add(e);                        
                    }
                    else if (e.connected1.equaloverride(next) && !e.connected2.beenSearched) {
                        breadthList.add(e.connected2);
                        cameFromEdge.put(e.connected2.cellCode(), new Edge(next, e.connected2));
                        displayEdge = e;
                        fixEdges.add(e);
                        //pathEdges.add(e);
                    }
                }
                pathEdges.add(displayEdge);
                next.beenSearched = true;
                return path;
            }
        }
        return path;
    }
    public ArrayList<Edge> depthSearch(Cell target) {

        if (depthList.size() > 0) {
            Cell next = depthList.peek();
            if (next.beenSearched) {
                depthList.pop();
                return path;
            }
            else if (next.equaloverride(target)) {
                return reconstruct(cameFromEdge, next);
            }
            else {
                Edge displayEdge = new Edge(next, next);
                for (Edge e: edgesInTree) {
                    if (e.connected2.equaloverride(next) && !e.connected1.beenSearched) {
                        depthList.push(e.connected1);
                        cameFromEdge.put(e.connected1.cellCode(), new Edge(next, e.connected1));
                        displayEdge = e;
                        fixEdges.add(e);
                        //pathEdges.add(e);                        
                    }
                    else if (e.connected1.equaloverride(next) && !e.connected2.beenSearched) {
                        depthList.push(e.connected2);
                        cameFromEdge.put(e.connected2.cellCode(), new Edge(next, e.connected2));
                        displayEdge = e;
                        fixEdges.add(e);
                        //pathEdges.add(e);
                    }
                }
                pathEdges.add(displayEdge);
                next.beenSearched = true;
                return path;
            }
        }
        return path;



    }
    public ArrayList<Edge> reconstruct(HashMap<Integer, Edge> path, Cell target) {
        int rep = target.cellCode();
        ArrayList<Edge> ret = new ArrayList<Edge>();
        while (rep > 0) {
            Edge e = path.get(rep);
            ret.add(e);
            rep = e.connected1.cellCode();

        }
        return ret;

    }
    public WorldScene makeScene() {
        WorldScene scene = new WorldScene(WORLD_WIDTH, WORLD_HEIGHT);
        scene.placeImageXY(new RectangleImage(WORLD_WIDTH, WORLD_HEIGHT, "solid", 
                new Color(212, 212, 212)), 
                WORLD_WIDTH / 2, WORLD_HEIGHT / 2); 
        for (Edge e : this.edgesInTree) {
            Cell c = e.connected1;
            Cell c2 = e.connected2;
            scene.placeImageXY(c.cellImage(), c.x * CELL_WIDTH + CELL_WIDTH / 2,
                    c.y * CELL_HEIGHT + CELL_HEIGHT / 2);

            scene.placeImageXY(c.cellImage(), c2.x * CELL_WIDTH + CELL_WIDTH / 2,
                    c2.y * CELL_HEIGHT + CELL_HEIGHT / 2);
        }

        for (Edge e : this.edgesInTree) {
            //get x and y coord for removing wall
            int x1 = e.connected1.x * CELL_WIDTH + CELL_WIDTH / 2;
            int x2 = e.connected2.x * CELL_WIDTH + CELL_WIDTH / 2;
            int x = (x1 + x2) / 2; 

            int y1 = e.connected1.y * CELL_HEIGHT + CELL_HEIGHT / 2;
            int y2 = e.connected2.y * CELL_HEIGHT + CELL_HEIGHT / 2;
            int y = (y1 + y2) / 2;

            scene.placeImageXY(e.edgeImage(MazeWorld.BACKGROUND), x, y);
        }
        //makes the view of the searched paths
        if (view) {
            for (Edge e : this.pathEdges) {
                //get x and y coord for removing wall
                int x1 = e.connected1.x * CELL_WIDTH + CELL_WIDTH / 2;
                int x2 = e.connected2.x * CELL_WIDTH + CELL_WIDTH / 2;
                int x = (x1 + x2) / 2; 

                int y1 = e.connected1.y * CELL_HEIGHT + CELL_HEIGHT / 2;
                int y2 = e.connected2.y * CELL_HEIGHT + CELL_HEIGHT / 2;
                int y = (y1 + y2) / 2;

                scene.placeImageXY(e.edgeImage(new Color(158, 204, 255)), x, y);
            }

            for (Edge e: fixEdges) {
                int x1 = e.connected1.x * CELL_WIDTH + CELL_WIDTH / 2;
                int x2 = e.connected2.x * CELL_WIDTH + CELL_WIDTH / 2;
                int x = (x1 + x2) / 2; 

                int y1 = e.connected1.y * CELL_HEIGHT + CELL_HEIGHT / 2;
                int y2 = e.connected2.y * CELL_HEIGHT + CELL_HEIGHT / 2;
                int y = (y1 + y2) / 2;

                scene.placeImageXY(e.fixEdge(new Color(158, 204, 255)), x, y);
            }
        }
        for (Edge e : this.path) {
            //get x and y coord for removing wall
            int x1 = e.connected1.x * CELL_WIDTH + CELL_WIDTH / 2;
            int x2 = e.connected2.x * CELL_WIDTH + CELL_WIDTH / 2;
            int x = (x1 + x2) / 2; 

            int y1 = e.connected1.y * CELL_HEIGHT + CELL_HEIGHT / 2;
            int y2 = e.connected2.y * CELL_HEIGHT + CELL_HEIGHT / 2;
            int y = (y1 + y2) / 2;

            scene.placeImageXY(e.edgeImage(Color.BLUE), x, y);
        }


        scene.placeImageXY(new RectangleImage(CELL_WIDTH - 2, CELL_HEIGHT - 2,
                "solid", new Color(34, 146, 0)), 
                CELL_WIDTH / 2, CELL_HEIGHT / 2);
        scene.placeImageXY(new RectangleImage(CELL_WIDTH - 2, CELL_HEIGHT - 2,
                "solid", new Color(81, 9, 129)), 
                (MAZE_WIDTH - 1) * CELL_WIDTH + CELL_WIDTH / 2,
                (MAZE_HEIGHT - 1) * CELL_HEIGHT + CELL_HEIGHT / 2);
        if (manual) {

            scene.placeImageXY(this.player.playerImage(), 
                    this.player.on.x * CELL_WIDTH + CELL_WIDTH / 2, 
                    this.player.on.y * CELL_WIDTH + CELL_WIDTH / 2);
        }

        return scene;

    }

    public void onTick() {
        if (breadth) {
            this.path = breadthSearch(exit);
        }
        else if (depth) {
            this.path = depthSearch(exit);
        }
    }
    public Player movePlayer(Player p, ArrayList<Edge> paths, String ke) {
        int x = p.on.x;
        int y = p.on.y;

        if (ke.equals("up")) {
            y--;
        }
        else if (ke.equals("left")) {
            x--;
        }
        else if (ke.equals("right")) {
            x++;
        }
        else if (ke.equals("down")) {
            y++;
        }
        Cell c = new Cell(x, y);
        for (Edge e: paths) {
            if (e.connected1.equaloverride(c) && e.connected2.equaloverride(p.on)) {
                return new Player(e.connected1);
            }
            else if (e.connected1.equaloverride(p.on) && e.connected2.equaloverride(c)) {
                return new Player(e.connected2);
            }
        }
        return new Player(p.on);

    }
    public void onKeyEvent(String ke) {
        if (ke.equals("d")) {
            //only lets u do 1 of the 3 at a time
            depth = !(breadth || manual);
        }
        else if (ke.equals("b")) {
            breadth = !(depth || manual);
        }
        else if (ke.equals("m")) {
            manual = !(depth || breadth);
        }
        else if (ke.equals("v")) {
            view = !view;
        }
        //clears the searches currently being done
        else if (ke.equals("c")) {
            this.depth = false;
            this.breadth = false;
            this.manual = false;
            this.depthList = new Stack<Cell>();
            depthList.push(entrance);
            this.breadthList = new ArrayList<Cell>();
            breadthList.add(entrance);
            cameFromEdge = new HashMap<Integer, Edge>();
            for (Edge e: pathEdges) {
                e.connected1.beenSearched = false;
                e.connected2.beenSearched = false;
            }

            this.path = new ArrayList<Edge>();
            this.pathEdges = new ArrayList<Edge>();
            this.fixEdges = new ArrayList<Edge>();


        }
        else if (ke.equals("up")) {
            this.player = movePlayer(this.player, this.edgesInTree, ke);
        }
        else if (ke.equals("down")) {
            this.player = movePlayer(this.player, this.edgesInTree, ke);
        }
        else if (ke.equals("left")) {
            this.player = movePlayer(this.player, this.edgesInTree, ke);
        }
        else if (ke.equals("right")) {
            this.player = movePlayer(this.player, this.edgesInTree, ke);
        }
        else if (ke.equals("r")) {
            MazeWorld maze = new MazeWorld();
            this.representatives = maze.representatives;
            this.worklist = maze.worklist;

            this.cameFromEdge = maze.cameFromEdge;
            this.breadthList = maze.breadthList;
            this.depthList = maze.depthList;

            this.edgesInTree = maze.edgesInTree;
            this.path = maze.path;
            this.pathEdges = maze.pathEdges;
            this.fixEdges = maze.fixEdges;

            this.depth = maze.depth;
            this.breadth = maze.breadth;
            this.manual = maze.manual;
            this.view = maze.view;

            this.exit = maze.exit;
            this.player = maze.player;
        }

    }

}
//represents grid of Maze
class Grid<T> {
    ArrayList<ArrayList<T>> grid;

    Grid() {
        this.grid = new ArrayList<ArrayList<T>>();
    }
}
//Creates a grid of the cell maze
class CellGrid extends Grid<Cell> {
    CellGrid() {
        ArrayList<ArrayList<Cell>> grid = new ArrayList<ArrayList<Cell>>();
        for (int y = 0; y < MazeWorld.MAZE_HEIGHT; y++) {
            grid.add(new ArrayList<Cell>());
            for (int x = 0; x < MazeWorld.MAZE_WIDTH; x++) {
                grid.get(y).add(new Cell(x, y));
            }

        }
        this.grid = grid;
    }
}


class ExamplesMazeWorld {

    Cell cell0 = new Cell(0, 0);
    Cell cell1 = new Cell(1, 1);
    Cell cell2 = new Cell(2, 2);
    Cell cell22 = new Cell(2, 2);
    Cell cell3 = new Cell(3, 3);
    Cell cell4 = new Cell(4, 4);
    Edge c1 = new Edge(cell1, cell2);
    Edge c2 = new Edge(cell3, cell4);
    Cell cell5 = new Cell(200, 200);
    Edge c3 = new Edge(cell5, cell5);
    Edge c4 = new Edge(cell2, cell3);
    Cell cell6 = new Cell(10, 16);
    Cell cell7 = new Cell(10, 16);
    Edge c5 = new Edge(cell6, cell7);
    Edge c123 = new Edge(cell7, cell7);

    boolean testCellCode(Tester t) {
        return t.checkExpect(cell1.cellCode(), 26) &&
                t.checkExpect(cell2.cellCode(), 52) &&
                t.checkExpect(cell22.cellCode(), 52) &&
                t.checkExpect(cell3.cellCode(), 78) &&
                t.checkExpect(cell4.cellCode(), 104);
    }

    boolean testcompareTo(Tester t) {
        c1.weight = 20;
        c2.weight = 10;
        return t.checkExpect(c1.compareTo(c2), 10);
    }
    boolean testcompareTo2(Tester t) {
        c1.weight = 0;
        c2.weight = 0;
        return t.checkExpect(c1.compareTo(c2), 0);
    }

    boolean testcompareTo3(Tester t) {
        c1.weight = -20;
        c2.weight = -15;
        return t.checkExpect(c1.compareTo(c2), -5);
    }

    boolean testEdgeImage(Tester t) {
        return t.checkExpect(c1.edgeImage(MazeWorld.BACKGROUND), new RectangleImage(0, 0,
                "solid", new Color(212, 212, 212))) &&
                t.checkExpect(c2.edgeImage(new Color(200, 130, 140)), new RectangleImage(0, 0,
                        "solid", new Color(200, 130, 140))) &&
                t.checkExpect(c3.edgeImage(new Color(100, 200, 250)), new RectangleImage(38, 38,
                        "solid", new Color(100, 200, 250))) &&
                t.checkExpect(c4.edgeImage(new Color(20, 30, 40)), new RectangleImage(0, 0,
                        "solid", new Color(20, 30, 40))) &&
                t.checkExpect(c5.edgeImage(new Color(212, 212, 212)), new RectangleImage(38, 78,
                        "solid", new Color(212, 212, 212)));

    }

    boolean testFixEdge(Tester t) {
        return t.checkExpect(c1.fixEdge(MazeWorld.BACKGROUND), new RectangleImage(0, 0,
                "solid", new Color(212, 212, 212))) &&
                t.checkExpect(c2.fixEdge(new Color(200, 130, 140)), new RectangleImage(0, 0,
                        "solid", new Color(200, 130, 140))) &&
                t.checkExpect(c3.fixEdge(new Color(100, 200, 250)), new RectangleImage(38, 38,
                        "solid", new Color(100, 200, 250))) &&
                t.checkExpect(c4.fixEdge(new Color(20, 30, 40)), new RectangleImage(0, 0,
                        "solid", new Color(20, 30, 40))) &&
                t.checkExpect(c5.fixEdge(new Color(212, 212, 212)), new RectangleImage(38, 4,
                        "solid", new Color(212, 212, 212)));
    }
    boolean testEqualOverride(Tester t) {
        return t.checkExpect(cell1.equaloverride(c2), false) &&
                t.checkExpect(cell1.equaloverride(cell1), true) &
                t.checkExpect(cell1.equaloverride(cell2), false) &&
                t.checkExpect(cell2.equaloverride(cell22), true);
    }

    boolean testCellImage(Tester t) {
        return t.checkExpect(cell1.cellImage(), new RectangleImage(MazeWorld.CELL_WIDTH, 
                MazeWorld.CELL_HEIGHT, "outline", Color.GRAY)) &&
                t.checkExpect(cell2.cellImage(), new RectangleImage(MazeWorld.CELL_WIDTH, 
                        MazeWorld.CELL_HEIGHT, "outline", Color.GRAY));
    }

    MazeWorld world2;
    void initAlgo() {
        world2 = new MazeWorld();

    }
    void testAlgo(Tester t) {
        this.initAlgo();
        t.checkExpect(world2.worklist.size(), 0);
        t.checkExpect(world2.edgesInTree.size(), MazeWorld.MAZE_WIDTH * MazeWorld.MAZE_HEIGHT - 1);
    }

    void initOnTick() {
        breadth = new MazeWorld();
        list11 = new ArrayList<Cell>();
        breadth.breadthList = list11;
        list22 = new HashMap<Integer, Edge>();
        breadth.cameFromEdge = list22;
        asdb = new Stack<Cell>();
    }

    void testOnTick(Tester t) {
        this.initOnTick();
        breadth.onTick();
        breadth.onKeyEvent("b");
        breadth.onKeyEvent("d");
        t.checkExpect(breadth.breadth, true);
        t.checkExpect(breadth.depth, false);
        breadth.onKeyEvent("r");
        t.checkExpect(breadth.breadth, false);
        breadth.onKeyEvent("d");
        t.checkExpect(breadth.depth, true);
        breadth.onKeyEvent("c");
        t.checkExpect(breadth.depth, false);
        breadth.onKeyEvent("r");
        breadth.onKeyEvent("d");
        breadth.onKeyEvent("v");
        t.checkExpect(breadth.view, false);
        breadth.onKeyEvent("v");
        t.checkExpect(breadth.view, true);
    }

    void testOnKeyEvent(Tester t) {
        this.initOnTick();
        breadth.onTick();
        breadth.onKeyEvent("b");
        t.checkExpect(breadth.breadth, true);
        breadth.onKeyEvent("r");
        t.checkExpect(breadth.breadth, false);
        breadth.onKeyEvent("d");
        t.checkExpect(breadth.depth, true);
        breadth.onKeyEvent("c");
        t.checkExpect(breadth.depth, false);
        breadth.onKeyEvent("r");
        breadth.onKeyEvent("d");
        breadth.onKeyEvent("v");
        t.checkExpect(breadth.view, false);
        breadth.onKeyEvent("v");
        t.checkExpect(breadth.view, true);
    }

    MazeWorld pre = new MazeWorld();
    HashMap<String, String> hashmap1 = new HashMap<String, String>();
    void initHashMap1() {
        hashmap1.put("A", "E");
        hashmap1.put("B", "A");
        hashmap1.put("C", "E");
        hashmap1.put("D", "E");
        hashmap1.put("E", "E");
        hashmap1.put("F", "F");
    }

    //tests the find method in algo
    boolean testFind(Tester t) {
        this.initHashMap1();
        return t.checkExpect(pre.find(hashmap1, "A"), "E") &&
                t.checkExpect(pre.find(hashmap1, "B"), "E") &&
                t.checkExpect(pre.find(hashmap1, "F"), "F");
    }

    void testUnion(Tester t) {
        this.initHashMap1();
        pre.union(hashmap1, "A", "F");
        pre.union(hashmap1, "B", "E");
        t.checkExpect(pre.find(hashmap1, "A"),  "F");
        t.checkExpect(pre.find(hashmap1, "B"),  "E");
    }

    MazeWorld world123 = new MazeWorld();
    public boolean testmakeScene(Tester t) {
        return t.checkExpect(world123.makeScene().width, 1000) &&
                t.checkExpect(world123.makeScene().height, 600);

    }

    MazeWorld breadth;
    ArrayList<Cell> list11;
    HashMap<Integer, Edge> list22;
    void initBreadth() {
        breadth = new MazeWorld();
        list11 = new ArrayList<Cell>();
        breadth.breadthList = list11;
        list22 = new HashMap<Integer, Edge>();
        breadth.cameFromEdge = list22;
    }

    Cell cell10 = new Cell(80, 80);



    void testBreadthSearch(Tester t) {
        this.initBreadth();
        t.checkExpect(breadth.breadthSearch(cell1), new ArrayList<Edge>());
        list11.add(cell0);
        t.checkExpect(breadth.breadthSearch(cell2), new ArrayList<Edge>());
        list11.add(cell1);
        t.checkExpect(breadth.breadthSearch(cell4), new ArrayList<Edge>());
        list11.add(cell2);
        t.checkExpect(breadth.breadthSearch(cell3), new ArrayList<Edge>());
        list11.add(cell3);
        t.checkExpect(breadth.breadthSearch(cell1), new ArrayList<Edge>());
        list22.put(0, c1);
        t.checkExpect(breadth.breadthSearch(cell10), new ArrayList<Edge>());
        list22.put(1, c2);
        t.checkExpect(breadth.breadthSearch(cell22), new ArrayList<Edge>());
        list22.put(2, c3);
        t.checkExpect(breadth.breadthSearch(cell6), new ArrayList<Edge>());
        list22.put(3, c3);
        t.checkExpect(breadth.breadthSearch(cell7), new ArrayList<Edge>());
        list22.put(4, c4);
        list22.put(5, c5);
        t.checkExpect(breadth.breadthSearch(cell10), new ArrayList<Edge>());
    }

    MazeWorld depth;
    Stack<Cell> asdb;
    void initDepth() {
        depth = new MazeWorld();
        asdb = new Stack<Cell>();
        depth.depthList = asdb;
        list22 = new HashMap<Integer, Edge>();
        depth.cameFromEdge = list22;
    }

    void testDepthSearch(Tester t) {
        this.initDepth();
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell0);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell1);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell2);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell3);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell4);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell5);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        asdb.add(cell6);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());
        list22.put(0, c1);
        t.checkExpect(depth.depthSearch(cell0), new ArrayList<Edge>());

    }
    MazeWorld test = new MazeWorld();
    HashMap<Integer, Edge> list1231 = new HashMap<Integer, Edge>();

    boolean testReconstruct(Tester t) {
        list1231.put(0, c1);
        list1231.put(1, c2);
        list1231.put(1, c3);
        list1231.put(1, c4);
        list1231.put(1, c5);
        return t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>()) &&
                t.checkExpect(test.reconstruct(list1231, cell0), new ArrayList<Edge>());

    }


    public static void main(String[] argv) {
        MazeWorld w = new MazeWorld();
        w.bigBang(MazeWorld.WORLD_WIDTH, MazeWorld.WORLD_HEIGHT, .001);
    }
}