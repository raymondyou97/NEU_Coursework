import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { FormEntryLocationComponent } from './form-entry-location.component';

describe('FormEntryLocationComponent', () => {
  let component: FormEntryLocationComponent;
  let fixture: ComponentFixture<FormEntryLocationComponent>;

  beforeEach(async(() => {
    TestBed.configureTestingModule({
      declarations: [ FormEntryLocationComponent ]
    })
    .compileComponents();
  }));

  beforeEach(() => {
    fixture = TestBed.createComponent(FormEntryLocationComponent);
    component = fixture.componentInstance;
    fixture.detectChanges();
  });

  it('should create', () => {
    expect(component).toBeTruthy();
  });
});
