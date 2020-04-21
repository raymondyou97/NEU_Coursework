import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { FormEntryPriceComponent } from './form-entry-price.component';

describe('FormEntryPriceComponent', () => {
  let component: FormEntryPriceComponent;
  let fixture: ComponentFixture<FormEntryPriceComponent>;

  beforeEach(async(() => {
    TestBed.configureTestingModule({
      declarations: [ FormEntryPriceComponent ]
    })
    .compileComponents();
  }));

  beforeEach(() => {
    fixture = TestBed.createComponent(FormEntryPriceComponent);
    component = fixture.componentInstance;
    fixture.detectChanges();
  });

  it('should create', () => {
    expect(component).toBeTruthy();
  });
});
