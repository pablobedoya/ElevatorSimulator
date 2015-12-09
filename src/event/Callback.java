package event;

/**
 * Callback common interface
 */
@FunctionalInterface
public interface Callback<T> {
    void run(T data);
}