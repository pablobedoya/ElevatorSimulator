package core;

/**
 * Objeto de estado do elevador
 */
public class ElevatorStatus {
    int currentFloor = 1; // Piso atual
    Direction direction = Direction.UP; // Direção
    int targetFloor = 0; // Piso de destino
    boolean isOpen = false; // Porta do elevador aberta
    boolean isMoving = true; // Elevador em movimento, o padrão é true, de modo que ao começar a subir, as portas sejam abertas
}
