package event;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * Event Generator base class
 * All classes want to get the event listeners / transmit capabilities need to extend this base class
 */
public class EventEmitter {
    /**
     * Adding event listeners
     * @param type
     * @param callback
     */
    public void on(EventType type, Callback callback)  {
        List<Callback> callbacks = getCallbacks(type);
        callbacks.add(callback);
    }

    /**
     * Sends the specified event
     * @param type
     * @param data
     * @param <T>
     */
    public <T> void emit(EventType type, T... data){
        List<Callback> callbacks = getCallbacks(type);
        callbacks.stream().forEach( callback -> callback.run(data.length>0?data[0]:null));
    }

    private Map<EventType,List<Callback>> callbackMap = new HashMap<EventType,List<Callback>>();

    /**
     * Get a list of specified event type callback function
     * If you do not list, create a (lazy initialization) now
     * @param type
     * @return
     */
    private List<Callback> getCallbacks(EventType type){
        List<Callback> callbacks = callbackMap.get(type);
        if(callbacks == null){
            callbacks = new LinkedList<Callback>();
            callbackMap.put(type, callbacks);
        }

        return callbacks;
    }
}
