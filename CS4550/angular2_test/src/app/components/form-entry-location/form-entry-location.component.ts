import { Component, OnInit, Output, EventEmitter } from '@angular/core';

@Component({
	selector: 'form-entry-location',
	templateUrl: './form-entry-location.component.html',
	styleUrls: ['./form-entry-location.component.css']
})
export class FormEntryLocationComponent implements OnInit {
	public location: string;

	@Output() locationValue = new EventEmitter<string>();
	@Output() previousPageValue = new EventEmitter<boolean>();
	@Output() skipValue = new EventEmitter<boolean>();
	
	constructor() { }

	ngOnInit() {
	}

	emitResponse() {
		this.locationValue.emit(this.location);
	}

	emitBackResponse() {
		this.previousPageValue.emit(false);
	}

	emitSkipResponse() {
		this.skipValue.emit(true);
	}
}
