import { Component, OnInit, Output, EventEmitter } from '@angular/core';

@Component({
	selector: 'form-entry-price',
	templateUrl: './form-entry-price.component.html',
	styleUrls: ['./form-entry-price.component.css']
})
export class FormEntryPriceComponent implements OnInit {
	public price: string;

	@Output() priceValue = new EventEmitter<string>();
	@Output() previousPageValue = new EventEmitter<boolean>();
	@Output() skipValue = new EventEmitter<boolean>();
	
	constructor() { }

	ngOnInit() {
	}

	emitResponse() {
		this.priceValue.emit(this.price);
	}

	emitBackResponse() {
		this.previousPageValue.emit(false);
	}

	emitSkipResponse() {
		this.skipValue.emit(true);
	}
}
