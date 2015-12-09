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
	/*@	requires type != null;
      @	requires callback != null;
      @ assignable callbacks;
      @ ensures callbacks.size() == \old(callbacks.size() + 1)
	  @      && callbacks.get(\old(callbacks.size()+1)).equals(callback); @*/
    @SuppressWarnings("rawtypes")
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
    @SuppressWarnings({ "rawtypes", "unchecked" })
	public <T> void emit(EventType type, T... data){
        List<Callback> callbacks = getCallbacks(type);
        callbacks.stream().forEach( callback -> callback.run(data.length>0?data[0]:null));
    }

    @SuppressWarnings("rawtypes")
	private Map<EventType,List<Callback>> callbackMap = new HashMap<EventType,List<Callback>>();

    /**
     * Get a list of specified event type callback function
     * If you do not list, create a (lazy initialization) now
     * @param type
     * @return
     */
    /*@	requires type != null;
      @ assignable callbacks;
      @ ensures callbacks.size() == \old(callbacks.size() + 1);
      @ ensures \result == callbacks; @*/
    @SuppressWarnings("rawtypes")
	private List<Callback> getCallbacks(EventType type){
        List<Callback> callbacks = callbackMap.get(type);
        if(callbacks == null){
            callbacks = new LinkedList<Callback>();
            callbackMap.put(type, callbacks);
        }

        return callbacks;
    }
}
