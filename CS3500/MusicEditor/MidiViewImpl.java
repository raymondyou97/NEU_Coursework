package cs3500.music.view;

import java.util.ArrayList;
import java.util.Set;
import java.util.TreeMap;
import cs3500.music.model.*;
import javax.sound.midi.*;


/**
 * A skeleton for MIDI playback
 */

public class MidiViewImpl implements MusicView {
  IMusicModel<Note> model;
  private final Synthesizer synthesizer;
  private final Receiver receiver;

  /**
   * Constructor
   * @param model
   * @throws MidiUnavailableException
   */
  public MidiViewImpl(IMusicModel<Note> model) throws MidiUnavailableException {
    this.model = model;
    this.synthesizer = MidiSystem.getSynthesizer();
    this.receiver = synthesizer.getReceiver();
    this.synthesizer.open();
  }


	/**
	 * Convenience constructor for MockMidiDevice
	 * @param model
   * @param synthesizer
	 * @throws MidiUnavailableException
   */
	public MidiViewImpl(IMusicModel<Note> model, Synthesizer synthesizer)
          throws MidiUnavailableException {
		this.model = model;
		this.synthesizer = synthesizer;
		this.receiver = synthesizer.getReceiver();
		this.synthesizer.open();
	}

  /**
   * Plays a note according to that note's attributes such as instrument, pitch value, and volume
   * @param note
   * @throws InvalidMidiDataException
   */
  public void playNote(Note note) throws InvalidMidiDataException {
    MidiMessage start = new ShortMessage(ShortMessage.NOTE_ON,
            note.getInstrument(),
            note.getPitchValue(), note.getVolume());
    MidiMessage stop = new ShortMessage(ShortMessage.NOTE_OFF, note
            .getInstrument(), note
            .getPitchValue(), note.getVolume());
    this.receiver.send(start, this.model.getTempo() * note.getStartBeat());
    this.receiver.send(stop, this.model.getTempo() * note.getEndBeat());
  }


  /**
   * Relevant classes and methods from the javax.sound.midi library: <ul> <li>{@link
   * MidiSystem#getSynthesizer()}</li> <li>{@link Synthesizer} <ul> <li>{@link
   * Synthesizer#open()}</li> <li>{@link Synthesizer#getReceiver()}</li> <li>{@link
   * Synthesizer#getChannels()}</li> </ul> </li> <li>{@link Receiver} <ul> <li>{@link
   * Receiver#send(MidiMessage, long)}</li> <li>{@link Receiver#close()}</li> </ul> </li>
   * <li>{@link MidiMessage}</li> <li>{@link ShortMessage}</li> <li>{@link MidiChannel} <ul>
   * <li>{@link MidiChannel#getProgram()}</li> <li>{@link MidiChannel#programChange(int)}</li>
   * </ul> </li> </ul>
   *
   * @see <a href="https://en.wikipedia.org/wiki/General_MIDI">
   *   https://en.wikipedia.org/wiki/General_MIDI
   * </a>
   */

  /**
   * Allows the user to begin seeing the view.
   */
  @Override
  public void initialize() {
    // nothing
  }

  /**
   * Makes all notes in the model audible, according to each note's fields.
   */
	@Override
	public void displayView() {
	  TreeMap<Integer, ArrayList<Note>> mapRetrieveMusic = this.model.retrieveMusic();

	  Set<Integer> setOfKeys = mapRetrieveMusic.keySet();
	  ArrayList<Integer> keys = new ArrayList<>();
	  for (Integer i : setOfKeys) {
		keys.add(i);
	  }

	  int keysIndex = 0;
	  int currentKey = keys.get(keysIndex);
	  ArrayList<Note> listOfNote = mapRetrieveMusic.get(currentKey);

	  for (int i = 0; keysIndex < keys.size(); i++) {
		// for the very last list
		if (keysIndex >= keys.size() - 1) {
		  // for the very last note of the very last list
		  if (i >= listOfNote.size() - 1) {
			// plays the note
			try {
			  this.playNote(listOfNote.get(i));
			}
      catch (InvalidMidiDataException e) {
        System.out.println("Invalid Midi data; could not play given note");
			}
      catch (IndexOutOfBoundsException e) {
      }
			keysIndex = keys.size();
		  }

		  else {
			// keeps playing note (i increases) until reaches the last note
			try {
			  this.playNote(listOfNote.get(i));
			} catch (InvalidMidiDataException e) {
        System.out.println("Invalid Midi data; could not play given note");
      }
		  }
		}
		else {
		  // once it reaches the last note
		  if (i > listOfNote.size() - 1) {
			  // increment keyIndex to get the the next arrayList of notes and start process again
			  keysIndex++;
			  // update index to beginning of list to begin process again
			  i = 0;
			  // update the list to the next arrayList of notes
			  listOfNote = mapRetrieveMusic.get(keys.get(keysIndex));
			}

		  // plays note
		  try {
			this.playNote(listOfNote.get(i));
		  } catch (InvalidMidiDataException e) {
        System.out.println("Invalid Midi data; could not play given note");
		  }
    }
    }
    try
    {
      Thread.sleep(this.model.getDuration() * this.model.getTempo() / 1000);
    }
    catch (InterruptedException e) {
      e.printStackTrace();
    }
    this.receiver.close();
	}
}
