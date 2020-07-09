package common;

public class Tuple2<V, U> {
    public final V x;
    public final U y;

    public Tuple2(V x, U y) {
        this.x = x;
        this.y = y;
    }

    public String toString() {
        return "(" + x + "," + y + ")";
    }
}
