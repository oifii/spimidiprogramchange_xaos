/*
 * Copyright (c) 2010-2016 Stephane Poirier
 *
 * stephane.poirier@oifii.org
 *
 * Stephane Poirier
 * 3532 rue Ste-Famille, #3
 * Montreal, QC, H2X 2L1
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

/*
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//the midinote.c, midiprogramchange.c and midicontinuouscontroller.c functions are portmidi equivalents of
//the midinote.jar, midiprogramchange.jar and midicontinuouscontroller.jar java class archives which are java sound midi equivalents of
//the midi_autohotkey-midi-function_example-note-on-note-off.ahk, midi_autohotkey-midi-function_example-program-change.ahk and midi_autohotkey-midi-function_example-continuous-controller.ahk 
//which are based on autohotkey.exe script midi library midi_autohotkey-midi-functions.ahk (that can be found in folder http://www.oifii.org/ns-org/nsd/ar/cp/midi_autohotkey/)
//
//portmidi, portable c midi library compiled with this project can be found in folder http://www.oifii.org/ns-org/nsd/ar/cp/midi_portmidi-src-217/ 
//
//java sound midi class archives equivalent examples (midinote.jar, midiprogramchange.jar and midicontinuouscontroller.jar) can be found in folders:
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_java-sound-midi_midinote/
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_java-sound-midi_midiprogramchange/
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_java-sound-midi_midicontinuouscontroller/
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_java-sound-midi_midicontinuouscontrollerraw/
//
//portmidi based midinote.c, midiprogramchange.c and midicontinuouscontroller.c can be found in folder:
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_portmidi-src-217_midinote/
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_portmidi-src-217_midiprogramchange/
//http://www.oifii.org/ns-org/nsd/ar/cp/midi_portmidi-src-217_midicontinuouscontroller/
//
//
//2011dec10, version 0.2, spi, revised to properly implement http://www.midi.org/techspecs/midimessages.php, in that table channel id is a value between 0 and 15 like inside this code but
//							   new main program interface parameters implements channel id for user with integer value between 1 and 16
//							   tests: when closing mididevice, opened with non-zero latency, cc 64 value 0 are sent on all channels
//							   default latency is zero if not specified, no undesirable cc 64 values will be sent
//							   -c option does not work for the time being, on exit always closes mididevice, this because atexit(exit) is called in pminit(), see pmwin.c, don't know the work around for now
//2011oct23, version 0.1, spi, created stephane.poirier@nakedsoftware.org
//
//2014may04, version 0.2, spi, renamed spimidiprogramchange.c
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
*/

#include "portmidi.h"
#include "porttime.h"
#include "stdlib.h"
#include "stdio.h"
#include "string.h"
#include "assert.h"
#include "math.h" //i.e. for min() and max() function calls
#include "windows.h" //i.e. for Sleep() function calls

//new parameters
char global_begin[1024]={"begin.ahk"};
char global_end[1024]={"end.ahk"};

#define INPUT_BUFFER_SIZE 100
#define OUTPUT_BUFFER_SIZE 0
#define DRIVER_INFO NULL
#define TIME_PROC ((int32_t (*)(void *)) Pt_Time)
#define TIME_INFO NULL
#define TIME_START Pt_Start(1, 0, 0) /* timer started w/millisecond accuracy */

#define STRING_MAX 80 /* used for console input */

int32_t latency = 0;


/* from oifii.org's autohotkey midi library, but adapted for channel id between 0 and 15
midiOutShortMsg(h_midiout, EventType, Channel, Param1, Param2) 
{ 
  ;h_midiout is handle to midi output device returned by midiOutOpen function 
  ;EventType and Channel are combined to create the MidiStatus byte.  
  ;MidiStatus message table can be found at http://www.midi.org/techspecs/midimessages.php 
  ;Possible values for EventTypes are NoteOn (N1), NoteOff (N0), CC, PolyAT (PA), ChanAT (AT), PChange (PC), Wheel (W) - vals in () are optional shorthand 
  ;SysEx not supported by the midiOutShortMsg call 
  ;Param3 should be 0 for PChange, ChanAT, or Wheel.  When sending Wheel events, put the entire Wheel value 
  ;in Param2 - the function will split it into it's two bytes 
  ;returns 0 if successful, -1 if not.  
  
  ;Calc MidiStatus byte combining a channel number between 0 and 15
  If (EventType = "NoteOn" OR EventType = "N1") 
    MidiStatus :=  144 + Channel 
  Else if (EventType = "NoteOff" OR EventType = "N0") 
    MidiStatus := 128 + Channel 
  Else if (EventType = "NoteOffAll") 
    ;MidiStatus := 124 + Channel
    MidiStatus := 176 + Channel
  Else if (EventType = "CC") 
    MidiStatus := 176 + Channel 
  Else if (EventType = "PolyAT" OR EventType = "PA") 
    MidiStatus := 160 + Channel 
  Else if (EventType = "ChanAT" OR EventType = "AT") 
    MidiStatus := 208 + Channel 
  Else if (EventType = "PChange" OR EventType = "PC") 
    MidiStatus := 192 + Channel 
  Else if (EventType = "Wheel" OR EventType = "W") 
  {  
    MidiStatus := 224 + Channel 
    Param2 := Param1 >> 8 ;MSB of wheel value 
    Param1 := Param1 & 0x00FF ;strip MSB, leave LSB only 
  } 

  ;Midi message Dword is made up of Midi Status in lowest byte, then 1st parameter, then 2nd parameter.  Highest byte is always 0 
  dwMidi := MidiStatus + (Param1 << 8) + (Param2 << 16) 
*/





/* midiprogram_stream exercises windows winmm API's stream mode */
/*    The winmm stream mode is used for latency>0, and sends
   timestamped messages. The timestamps are relative (delta) 
   times, whereas PortMidi times are absolute. Since peculiar
   things happen when messages are not always sent in advance,
   this function allows us to exercise the system and test it.
 */
//warning: the use of this timestamped stream of midi messages
//         provoques sending CC 64 value 0 twice to all channels 
//         tested by spi.
void midiprogram_stream(int latency, int deviceid, int close_mididevice_onexit, int channelid, int programnumber) 
{
    PmStream* midi;
	char line[80];
    PmEvent buffer[3];

    /* It is recommended to start timer before PortMidi */
    TIME_START;

	/* open output device */
    Pm_OpenOutput(&midi, 
                  deviceid, 
                  DRIVER_INFO,
                  OUTPUT_BUFFER_SIZE, 
                  TIME_PROC,
                  TIME_INFO, 
                  latency);
#ifdef DEBUG
    printf("Midi Output opened with %ld ms latency.\n", (long) latency);
#endif //DEBUG

    /* if we were writing midi for immediate output, we could always use
       timestamps of zero, but since we may be writing with latency, we
       will explicitly set the timestamp to "now" by getting the time.
       The source of timestamps should always correspond to the TIME_PROC
       and TIME_INFO parameters used in Pm_OpenOutput(). */
    buffer[0].timestamp = TIME_PROC(TIME_INFO); //now in ms
    buffer[0].message = Pm_Message((unsigned char)(192+channelid), (unsigned char)programnumber, (unsigned char)0); 

	Pm_Write(midi, buffer, 1);

	if(close_mididevice_onexit==TRUE)
	{
		/* close device (this not explicitly needed in most implementations) */
		Pm_Close(midi);
		Pm_Terminate();
		#ifdef DEBUG
			printf("done closing and terminating...\n");
		#endif //DEBUG
	}
}

//the purpose of creating nostream() version was to attempt to prevent cc 64 values being sent on all channels when closing mididevice
//by relying on Pm_WriteShort to send midi message instead of Pm_Write to send midi event (a midi message with timestamp) but did not
//find a way to send midi message without timestamp other than by specifying zero latency when opening the mididevice which provoques
//timestamps to be ignored later on when sending mesage onto this device and thereby prevents cc 64 value 0 to be sent on all channels
//upon closing mididevice.
void midiprogramchange_nostream(int latency, int deviceid, int close_mididevice_onexit, int channelid, int programnumber) 
{
    PmStream* midi;
	char line[80];
    PmEvent buffer[3];

    /* It is recommended to start timer before PortMidi */
    TIME_START;

	/* open output device */
    Pm_OpenOutput(&midi, 
                  deviceid, 
                  DRIVER_INFO,
                  OUTPUT_BUFFER_SIZE, 
                  TIME_PROC,
                  TIME_INFO, 
                  latency);
#ifdef DEBUG
    printf("Midi Output opened with %ld ms latency.\n", (long) latency);
#endif //DEBUG

    /* writing midi for immediate output, we use timestamps of zero */
    buffer[0].timestamp = -1;
    buffer[0].message = Pm_Message((unsigned char)(192+channelid), (unsigned char)programnumber, (unsigned char)0);

	Pm_WriteShort(midi, buffer[0].timestamp, buffer[0].message);

	if(close_mididevice_onexit==TRUE)
	{
		/* close device (this not explicitly needed in most implementations) */
		Pm_Close(midi);
		Pm_Terminate();
		#ifdef DEBUG
			printf("done closing and terminating...\n");
		#endif //DEBUG
	}

}


/* if caller alloc devicename like this: char devicename[STRING_MAX]; 
	then parameters are devicename and STRING_MAX respectively        */
int get_device_id(const char* devicename, int devicename_buffersize)
{
	int deviceid=-1;
	int i;
    for (i=0; i<Pm_CountDevices(); i++) 
	{
        const PmDeviceInfo* info = Pm_GetDeviceInfo(i);
 		if(strcmp(info->name, devicename)==0) 
		{
			deviceid=i;
			break;
		}
    }
	#ifdef DEBUG
		if(deviceid==-1)
		{
			printf("get_device_id(), did not find any matching deviceid\n");
		}
	#endif //DEBUG
	return deviceid;
}


void show_usage()
{
	int i;
    printf("Usage: midiprogramchange [-h] [-l latency-in-ms] [-d <device name>] <channel id> <program number>\n");
	printf("\n"); 
    printf("<device name> can be one of the following midi output devices:\n");
    for (i=0; i<Pm_CountDevices(); i++) 
	{
        const PmDeviceInfo* info = Pm_GetDeviceInfo(i);
        if (info->output) printf("%d: %s\n", i, info->name);
    }
    //printf("<channel id> is an integer between 1 and 16\n");
    printf("<channel id> is an integer between 0 and 15\n");
    printf("<program number> is an integer between 0 and 127\n");
	printf("Usage example specifying optional latency and output device, respectively 20ms and \"Out To MIDI Yoke:  1\", along with mandatory channel id and program number\n");
	printf("midiprogramchange -l 20 \"Out To MIDI Yoke:  1\" 1 60 2000 100\n");
	printf("Usage example not specifying optional latency and output device, in order to use the defaults, along with mandatory channel id and program number\n");
	printf("midiprogramchange 1 64\n");
   exit(0);
}

int main(int argc, char *argv[])
{
    int i = 0, n = 0, id=0;
    char line[STRING_MAX];

	int close_mididevice_onexit = FALSE;
	int latency_valid = FALSE;
    char devicename[STRING_MAX];
	int devicename_valid = FALSE;
	//int channelid = 0;
	//int channelid = 1; //default user specified channelid must be between 1 and 16
	int channelid = 0; //default user specified channelid must be between 0 and 15
	int channelid_valid = FALSE;
	int programnumber = 0;
	int programnumber_valid = FALSE;

	int deviceid=-1;
	const PmDeviceInfo* info;

    if(argc==1) show_usage();
    for (i = 1; i < argc; i++) 
	{
        if (strcmp(argv[i], "-h") == 0) 
		{
            show_usage();
        } 
		else if (strcmp(argv[i], "-l") == 0 && (i + 1 < argc)) 
		{
			//optional parameter, latency
            i = i + 1;
            latency = atoi(argv[i]);
            latency_valid = TRUE;
        } 
		else if ( (strcmp(argv[i], "-b") == 0 && (i + 1 < argc)) ||
				  (strlen(argv[i])>2) ) 
		{
			//optional parameter, devicename
			if(strcmp(argv[i], "-b") == 0){ i=i+1;}
            strcpy(global_begin, argv[i]);
            devicename_valid = TRUE;
        } 
		else if ( (strcmp(argv[i], "-e") == 0 && (i + 1 < argc)) ||
				  (strlen(argv[i])>2) ) 
		{
			//optional parameter, devicename
			if(strcmp(argv[i], "-e") == 0){ i=i+1;}
            strcpy(global_end, argv[i]);
            devicename_valid = TRUE;
        } 
		else if ( (strcmp(argv[i], "-d") == 0 && (i + 1 < argc)) ||
				  (strlen(argv[i])>2) ) 
		{
			//optional parameter, devicename
			if(strcmp(argv[i], "-d") == 0){ i=i+1;}
            strcpy(devicename, argv[i]);
            devicename_valid = TRUE;
        } 
		else if (strcmp(argv[i], "-c") == 0) 
		{
			//optional parameter, enabling option to close device every time this program is called
            i = i + 1;
            close_mididevice_onexit = TRUE;
        } 
		else if(i + 1 < argc)
		{
			//mandatory parameters
			channelid = atoi(argv[i]);
			//min(16, max(1, channelid)); //for user channelid is specified by an integer between 1 and 16
			min(15, max(0, channelid)); //for user channelid is specified by an integer between 0 and 15
			channelid_valid = TRUE;
			//channelid = channelid -1; //for the implementation channelid is specified by an integer between 0 and 15
			programnumber = atoi(argv[i+1]);	
			min(127, max(0, programnumber));
			programnumber_valid = TRUE;
			break;
		}
		else 
		{
            show_usage();
        }
    }

	ShellExecuteA(NULL, "open", global_begin, "", NULL, 0);

	#ifdef DEBUG
		if (sizeof(void *) == 8) 
			printf("64-bit machine.\n");
		else if (sizeof(void *) == 4) 
			printf ("32-bit machine.\n");
		printf("latency %ld\n", (long) latency);
		printf("device name %s\n", devicename);
		printf("channel id %ld\n", (long) (channelid+1));
		printf("program number %ld\n", (long) programnumber);
	#endif //DEBUG
	if(channelid_valid==TRUE &&
		programnumber_valid==TRUE)
	{

		if(latency_valid==FALSE)
		{
			latency = 0; //ms
		}
		if(devicename_valid==FALSE)
		{
			printf("warning wrong devicename format, replacing invalid devicename by default devicename\n");
			id = Pm_GetDefaultOutputDeviceID();
			info = Pm_GetDeviceInfo(id);
			strcpy(devicename, info->name);
			printf("device name %s\n", devicename);
		}
	}
	else
	{
		printf("warning invalid arguments format, exit(1)\n");
		show_usage();
	}

	deviceid = get_device_id(devicename, STRING_MAX);
	if(deviceid==-1) 
	{
		deviceid=Pm_GetDefaultOutputDeviceID();
		printf("warning wrong devicename syntax, replacing invalid devicename by default devicename\n");
		info = Pm_GetDeviceInfo(deviceid);
		strcpy(devicename, info->name);
		printf("device name %s\n", devicename);
	}

    /* send note */
    //midiprogramchange_stream(latency, deviceid, close_mididevice_onexit, channelid, programnumber);
    midiprogramchange_nostream(latency, deviceid, close_mididevice_onexit, channelid, programnumber);
	//main_test_output();

	ShellExecuteA(NULL, "open", global_end, "", NULL, 0);

	return 0;
}
